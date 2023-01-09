'''
Routines to process housekeeping data and write them to a FITS format file.
Based of functions for minipacket data extraction by R. McCurdy 2017-02-22.
P. Kaaret 2017-03-08 to 2017-10/18

2018-09-06 Local version modified by A.Zajczyk
  Information about packet sequence number, packet time and type is now being
  saved for each extracted science event. In addition to the standard information
  in the evt files:
    DPU_ID - dpu identification number
    TIME   - event arrival time
    PHA    - pulse height value of the event
  the following were added:
    PKT_SEQ  - packet sequence number
    PKT_TIME - packet time
    PKT_TYPE - packet type (for science events it should always be == 2)

2018-01-24 Local version modified by A.Zajczyk
  INPUT:
  <datadir>: full path to the directory containing data
  DEPRECATED: <file_base>: name of the data file to be analyzed (w or w/o .bin extension) or
    name of a text file containing list of files to be analyzed (w or w/o .bin ext).
    To indicate that the input file is a list name has to be preceded by @, i.e
    @<name_list_of_files>

  Commented out "print" statement for unknown packet type wher i0 invoked
'''

#REVISION 2.2

#JKB changed this version to perform CRC check before packet processing, skipping bad CRCs
#JKB changes 11-16-2018 changed HTIMES list to global to fix a bug duplicating header times in the DB. Added bin file to the header table to ID where headers are coming from.
#JKB 12-6-18 changed to text based log files. Experimenting with the code shows slowdown from accessing the databases too many times. SQl adds no needed functionality, so moving these logs to .txt affects nothing and just speeds up code. Still slowdown from holding the lists in memory, but querying SQL directly is still slower (IE is X in the DB, if no process X is slower than is X in the list). Change this code to run with actual database after repopulating.
#JKB 22:32 use sys to print log file now, also fixed minipacket counters. 
#JKB May 2019 - Major overhaul, now store offsets and truncated times to recreate event times after the fact, in SEARCHDB.py. Moved log files to subdirectory, now keeping a record of logs on the server (/logs). Implemented rotating hash logs for uniqueness check. 
#JKB 6/3/19 - MAJOR REVISION 2 - new database scheme, batch replacement of related software. Rev 1 Archived.
#JKB 6/28/19 - shutil backup scheme added
#JKB 7/25/2019 - REVISION 2.1 - another new duplication scheme. Due to discrete problems in v1 and v2, I'm revising this scheme again. Separate duplication logs has proven to be buggy occasionally, with the possibility of disruption between writing DB and writing logs. Additionally, it has been demonstrated that we DO get extremely late-time duplication, with September data re-arriving in May. Now will use the hash generated, combined with a counter, as a key for writing to the database. No changes to searchdb. only scidb and database are changed. DB write now happens multiple times for larger files to prevent the OS from killing it, but not so many times that the code slows down. 
# JKB 8/20/19  - added ssh line to transfer DB once a week.
# JKB 8/28/19 - code no longer writes to DB if there is an excessive CRC error rate. Currently 2%, based on CRC rates seen in files. At some point this will be rerun, to remove corrupted July data in the current DB. As such, I consider this revision 2.2
# JKB 8/4/20 - Minor edit. Changed backup directory to external drive.

import matplotlib.pyplot as plt
import os.path
from numpy import *
import pyfits
from datetime import datetime, timedelta, date
from pytz import timezone, utc
from os import listdir, remove
from sys import argv
import sys
import sqlite3
import glob
import pandas as pd
import hashlib
import shutil

#import resource
#resource.setrlimit(resource.RLIMIT_STACK, (2**29,-1))

def create_science_db(dbdir): #JKB
    os.chdir(dbdir)
    conn=sqlite3.connect('science.db')
    c=conn.cursor()
    c.execute('''CREATE TABLE EVENTS(TRUNCATED_TIME REAL,PHA INT,DPU_ID INT,PACKET_TIME REAL,TAG PRIMARY KEY)''')
    c.execute('''CREATE TABLE OFFSETS14(TIME_OFFSET_14 REAL,PKT_TIME_14 INT PRIMARY KEY)''')
    c.execute('''CREATE TABLE OFFSETS38(TIME_OFFSET_38 REAL,PKT_TIME_38 INT PRIMARY KEY)''')
    c.execute('''CREATE TABLE OFFSETS54(TIME_OFFSET_54 REAL,PKT_TIME_54 INT PRIMARY KEY)''')
    conn.commit()
    conn.close()

def write_db(dbdir,datadir): #added by Jesse
  os.chdir(dbdir)
  conn = sqlite3.connect('science.db')
  c = conn.cursor()
  c.executemany("""INSERT OR IGNORE INTO EVENTS (TRUNCATED_TIME, PHA, DPU_ID, PACKET_TIME, TAG) VALUES (?,?,?,?,?)""",
                           zip(all_etime,all_pulse,all_dpu_id,all_ptime,all_tags))
  c.executemany("""INSERT OR IGNORE INTO OFFSETS14 (TIME_OFFSET_14,PKT_TIME_14) VALUES (?,?)""",
                           zip(offsets14,pt14))
  c.executemany("""INSERT OR IGNORE INTO OFFSETS38 (TIME_OFFSET_38,PKT_TIME_38) VALUES (?,?)""",
                           zip(offsets38,pt38))
  c.executemany("""INSERT OR IGNORE INTO OFFSETS54 (TIME_OFFSET_54,PKT_TIME_54) VALUES (?,?)""",
                           zip(offsets54,pt54))
  # Save (commit) the changes
  conn.commit()
  # We can also close the connection if we are done with it.
  # Just be sure any changes have been committed or they will be lost.
  conn.close()
  #print 'DB write complete at'
  #print datetime.now()
  #print len(all_tags), 'rows written to science'
  os.chdir(datadir)

def bct_time_to_local(event_time):
# convert BCT times to unix times then to Central US time
  # BCT EDU time is seconds since Epoch 2000-01-01 TAI time (GPS time)
  epoch_linux = datetime(1970, 1, 1)   # reference for POSIX epoch
  epoch_linux = utc.localize(epoch_linux)   # POSIX localized to UTC
  epoch_bct = datetime(2000, 1, 1)    # reference epoch yr = 2000.0 for BCT EDU
  epoch_bct = utc.localize(epoch_bct)   # epoch localized to UTC
  leapseconds = 37.0 # GPS time is offset from UTC time because of leap seconds
  time_delta = timedelta(seconds=event_time-leapseconds) # create datetime object from event_time [sec]
  true_time = epoch_bct + time_delta # get event time in UTC date:time
  true_time_unix = (true_time - epoch_linux).total_seconds() # get seconds since POSIX for event_time
  return datetime.fromtimestamp(true_time_unix).strftime('%Y-%m-%d %H:%M:%S')


def init_crcccitt_tab(): #function from lib_crc.c to generate CRC validation table
  P_CCITT = 0x1021 #CRC polynomial
  crc_tabccitt = zeros(256, dtype=int)
  for i in range(256):
    crc = 0x0000
    c = ((i & 0xFFFF) << 8) & 0xFFFF
    for j in range(8):
      if (((crc ^ c) & 0x8000)):
        crc = ((crc << 1) ^ P_CCITT) & 0xFFFF
      else: crc = (crc << 1) & 0xFFFF
      c = (c << 1) & 0xFFFF
      crc_tabccitt[i] = (crc) & 0xFFFF
  return crc_tabccitt

def update_crc_ccitt(table, crc, c): #function from lib_crc.c to update CRC
  short_c = (c & 0xFF)
  tmp = ((crc >> 8) ^ short_c)
  crc = ((crc << 8) ^ table[tmp])
  return crc

def crc_check(table, packet, good_crc):
  test_crc = 0x0000
  for i in range(len(packet)):
    #packet is transport frame starting from sequence monotonic to end of packet
    test_crc = (update_crc_ccitt(table, test_crc, packet[i])) & 0xFFFF
    #print format(test_crc, '04X'), format(good_crc, '04X')
  if (test_crc == good_crc):
    return True
  else:
    return False

# def find_mp_time(mp_time_in, wave_time_in, epoch):
# # calculate time minipacket was created from truncated time
#   MAX_DELTA = int(64)
#   pkt_time = wave_time_in & 0xFFFFFFFE #strip time quality bit
#   mp_time = int(mp_time_in)
#   mp_time = int(mp_time/40) #10 bit second in minipacket
#   delta = mp_time - (pkt_time & 0x000003FF) #32 bit SCLK
#   if (delta > MAX_DELTA):
#     delta -= 0x0400
#   return pkt_time + delta + epoch #return minipacket time

def find_event_time(evt_time, packet_time): #removed epoch, which is time offset
# time offset handled in database search
# calculate time of X-ray event from truncated time in minipacket and system time from parent packet
# truncated event time is 15 bits in increments of 1/20 second
  et = evt_time / 20.0 # convert truncated event time to seconds
  # use high bits from packet time
  t = (int(packet_time) & 0xFFFFFC00) + et
  # packet time is written after events, if event time is later than packet time
  # then the packet time high bits incremented after the event occurred
  if t > (packet_time + 2) :
    t -= 0x400 # correct for this by subtracting one increment of the high bits
  #if t > (packet_time+2) : print evt_time, packet_time, packet_time & 0xFFFFFC00, et, t
  return t #+ epoch # return event time

#housekeeping code stripped out here by Jesse

class EVTdata(object):
# class to accumulate housekeeping (HK) data as one reads through a file

  def __init__(self): # initialization routine
  # create an event data object
    # setup dictionary that holds event data
    # each entry is the HK element name and a list with the values for the event
    self.d = {'TIME':[], 'DPU_ID':[], 'STAT':[], 'PHA':[], 'PKT_SEQ':[], 'PKT_TIME':[], 'PKT_TYPE':[], 'HDR_TIME':[]}

  def process_packet(self, tm, headtime, dpu_id, packet_time, timeoffset, pkt_seq, tag, dbdir, datadir, loud=1) :
  # process a science data packet and append data to the lists in the event data dictionary self.d
  # routine to process science mini packets
  # tm is the telemetry packet data starting with the first minipacket
  # dpu_id is the ID of the DPU that produced the packets
  # sys_time is the DPU time in the telemetry packet header
  # timeoffset is an array of offsets between DPU time and TAI time
  # The routine returns the number of event and ancillary minipackets.

    global all_tags, all_dpu_id, all_etime, all_pulse, all_ptime, pt54, pt38, pt14, offsets14, offsets38, offsets54
    nemp, namp, ncmp = 0, 0, 0 # number of minipackets (event, ancillary, counter)
    decode_length = 0 # number of bytes decoded
    length = len(tm)
    headtime2=str(headtime)[0:6]
    j = 0
    evtcntr = 1 #event counter, used for additional key component on the hash.
    #print 'length = ', length
    while (j < length-1): # only look for minipackets in this frame
      #print 'j=', j
      # byte 0 top 4 bits are the mini packet type
      mtype = ((tm[j] & 0xF0) >> 4)
      # byte 0 bottom 4 bits and byte 1 are length
      mlength = ((tm[j] & 0x0F) << 8) | ((tm[j+1]) & 0xFF)
      #print 'mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j)
      if (mtype == 0) : # 0 means fill data, skip rest of packet
        return nemp, namp, ncmp
      elif (mlength == 0) :
        if (loud > 0) : print '!!! Error: minipacket length of zero'
        if (loud > 0) : print 'mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j)
        break # kill while loop < breaking seems suboptimal here, but since length is vital for finding the next mini a zero ruins this code anyways....
      elif ((j+mlength) >= length) :
        if (loud > 0) : print '!!! Error: minipacket does not fit in packet'
        if (loud > 0) : print 'mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j), ' length=', length
        break # kill while loop 
      elif (mtype == 2): # HaloSat X-ray event minipacket
        nemp += 1 # chalk up another event minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF) # mini packet time
        # byte 4 is segmentation and MSF
        if (tm[j+4] & 0x80) == 0x80 :
          print 'Data are of questionable quality, j='+str(j)+'='+hex(j)
        #if (tm[j+4] & 0x10) == 0x10 :
        #  print 'EOF, j='+str(j)+'='+hex(j)
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00): mlength += 9
        else : print '*** Error MSF = ', msf
        # byte 5 is data packing 2=packed event data (4 bytes), 1=raw event data (7 bytes)
        # the previous line is incorrect
        #if (tm[j+5] & 0x01) == 0x01 :
        #  print 'Error RAW event data, j='+str(j)+'='+hex(j)
        #if loud : print 'Event minipacket time=', find_mp_time(mp_time, packet_time, 0), 'len=', mlength
        if ((j+mlength) > length): #JKB, new break check, 10/25/18
          if (loud > 0) : print '!!! Error: minipacket does not fit in packet'
          if (loud > 0) : print 'mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j), ' length=', length
          break
        for k in range(j+6, j+mlength-3, 4) :
          evt_time = (tm[k]<<7) | ((tm[k+1]&0xFE) >> 1) # 15 bit truncated event time
          # add data for this event to global lists: event_time, dpu_id, event_status, pulse_height
          # event_time = find_event_time(trunc_event_time, sys_time, timeoffset[packet_dpu_id])
          # event_time = find_event_time(evt_time, packet_time, 0)
          event_time = find_event_time(evt_time, packet_time)
          #if event_time < 1700 :
          #  print 'evt_time=', evt_time, hex(evt_time), ' packet_time=', packet_time, hex(packet_time), \
          #    ' event_time=', event_time
          #self.d['TIME'].append(event_time) # event time
          #self.d['DPU_ID'].append(dpu_id)
          event_status = ((tm[k+1]&0x01)<<2)+((tm[k+2]&0xC0)>>6)
          #self.d['STAT'].append(event_status) # 1=X-ray, 3=reset, 4=test
          pulse_height = ((tm[k+2]&0x3F)<<8) | ((tm[k+3]&0xFF))
          #self.d['PHA'].append(pulse_height)
          #self.d['PKT_SEQ'].append(pkt_seq)
          #self.d['PKT_TYPE'].append(pkt_type)
          #self.d['PKT_TIME'].append(pkt_time)
          etag=tag+'_'+str(evtcntr)
	  evtcntr+=1
          all_tags.append(etag)
          all_pulse.append(int(pulse_height))
          all_ptime.append(headtime2)
          all_dpu_id.append(int(dpu_id))
          all_etime.append(float(event_time)) #event_time, not tmp_time bug fixed 10/31/18 JKB - 4/28/19 JKB changed event time to not include offsets due to scrambled packet order
      elif (mtype == 12): # ancillary data minipacket
        namp += 1 # chalk up another ancillary minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF)
        # byte 4, 5 are segmentation and MSF
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00) : mlength += 9
        else : print '*** Error MSF = ', msf
        #if loud : print 'Ancillary data time=', find_mp_time(mp_time, packet_time, 0), 'len=', mlength
        # bytes 8 to 8+54 are BCT data with 4 sync bytes removed
        # bytes 14-17 are 32-bit time, unix for Willy, TAI for BCT
        utime = (tm[j+14]<<24)+(tm[j+15]<<16)+(tm[j+16]<<8)+(tm[j+17]<<0)
        # bytes 63-67 are command arrival time
        ctime = tm[j+63]*0.025+tm[j+64]+(tm[j+65]<<8)+(tm[j+66]<<16)+(tm[j+67]<<24)
        newtimeoffset = utime-ctime
        if dpu_id == 54:
          pt54.append(headtime2)
          offsets54.append(newtimeoffset)
        if dpu_id == 38:
          pt38.append(headtime2)
          offsets38.append(newtimeoffset)
        if dpu_id == 14:
          pt14.append(headtime2)
          offsets14.append(newtimeoffset)
        timeoffset[dpu_id] = newtimeoffset
        # QQQ include code to save aspect and orbit information
      elif (mtype == 3): # HaloSat counter data
        ncmp += 1 # another counter minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF)
        # byte 4 is segmentation and MSF
        if (tm[j+4] & 0x80) == 0x80 :
          print 'Data are of questionable quality, j='+str(j)+'='+hex(j)
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00) : mlength += 9
        else : print '*** Error MSF = ', msf
        #if loud : print 'Counter minipacket mp_time = ', mp_time, ' packet_time=', packet_time, ' msf=', msf, ' mlength=', mlength
        # if loud : print " ".join("{:02x}".format(c) for c in tm[j:j+mlength])
      else : # some other minipacket type
        print 'Unknown minipacket type', mtype, 'len=', mlength
        # print " ".join("{:02x}".format(c) for c in tm[j:i0+length])   # 2018-01-24 commented out
        #for kk in range(j, i0 + length) :
        #  print hex(tm[kk]),
        print
      # number of bytes decoded in this packet
      decode_length += mlength
      #move pointer ahead by length of mini packet
      j += mlength
    if decode_length != length :
      fillervariable=1  #error without something here
      #if loud : print '*** Not all data decoded sys_time=', packet_time, ' length=', length, ' decode_length=', decode_length
    if len(all_tags) > 500000:
	if crc_ratio < 0.03:
    		write_db(dbdir, datadir)
	else:
		print "Mid-file write aborted: "+str(100.0*crc_ratio)+" percent CRC error rate in file."
    	all_ptime=[]
    	all_dpu_id =[]
    	all_etime = []
    	all_tags = []
    	all_pulse=[]
    	pt38=[]
    	pt14=[]
    	pt54=[]
    	offsets14=[]
    	offsets54=[]
    	offsets38=[]
    return nemp, namp, ncmp


  def evtdata(self):
  # return the dictionary with the accumulated evt data
    return self.d

def process_tm(tm, fname, evtdata, dbdir, datadir, loud=False):
# extract event minipackets from HaloSat telemetry files
  timeoffset = zeros(64)-1 # 64 possible DPU IDs

  filelen = len(tm) # number of bytes in file
  print 'filelen = ', filelen
  i = 0 # pointer index
  ntm = 0 # number of FLEXI packets found
  nhp = 0 # keep track of number of housekeeping packets
  nsp = 0 # keep track of number of science packets
  nemp = 0 # keep track of number of event data minipackets
  namp = 0 # keep track of number of ancillary data minipackets
  ncmp = 0 # keep track of number of count data minipackets

  nbadcrc = 0 # keep track of bad CRC's
  flexi_seq = {}
  seq_time = {}


  crc_tabccitt = init_crcccitt_tab() #create CRC table
  badcrc_flexi_id = -1 # good CRC
  j=0
  global crc_ratio
  #hashdupe=0 #duplicate hashes 12/4/18 JKB - no longer functions. 7/28/19

  # go through file - remixed by JKB 4/27/19
  while (i < filelen):
    if ((tm[i]==0x35) and (tm[i+1]==0x2E) and (tm[i+2]==0xF8) and (tm[i+3]==0x53) and (tm[i+22] == 0xFA) and (tm[i+23] == 0xF3) and (tm[i+24] == 0x34) and (tm[i+25] == 0x03)): #merged both header/sync checks into one - JKB 4/27 
      # look for FLEXI sync pattern offset by 22 in index from header check, offset JKB addition
      # good sync pattern, so extract the packet):
      crc = (tm[i+26]<<8) | tm[i+27] # crc is bytes 4 and 5, moved by JKB 11/2/2018
      length = (tm[i+36]<<8) | tm[i+37] # record length, starts with first minipacket byte moved by JKB 11/2  
      packet_type = (tm[i+28] & 0xC0) >> 6 # packet type 0=panic, 2=science, 3=housekeeping
      dpu_id = ((tm[i+34]&0xFC)>>2) # DPU ID is bits 7:2 of byte 12, moved by JKB 11/2/18 
      flexi_id = (dpu_id << 2) | packet_type
      if crc_check(crc_tabccitt, tm[i+28:i+38+length], crc): #JKB 1/2/18 moved CRC check
        badcrc_flexi_id = -1 # good CRC
        ntm += 1 # have a new telemetry packet
        utime = (tm[i+10]<<24)+(tm[i+11]<<16)+(tm[i+12]<<8)+(tm[i+13]<<0)
        taitime=float(utime)+float(tm[i+14])*0.2
        packet_seq = ((tm[i+28] & 0x3F) << 8) | tm[i+29] # sequence number
       # system time is bytes 8, 9, 10, 11. LSB of 11 is quality flag
        packet_time = ((tm[i+30]&0xFF)<<24) | ((tm[i+31]&0xFF)<<16) | ((tm[i+32]&0xFF)<<8) | ((tm[i+33]&0xFE))
       # bytes 14-17 are 32-bit time, unix for Willy, TAI for BCT
        if ((tm[i+33]&0x01) == 1): # got a bad time flag
          bad_time = True
          if loud : print 'Bad Time!'
        if loud : print 'DPU = ', dpu_id, ' packet type, seq = ', packet_type, packet_seq
        epoch = ((tm[i+34]&0x03)<<8) | tm[i+35] # epoch is bits 1:0 of byte 12 and byte 13
        # check if the sequence number increments sequentially for each DPU/packet type
        
        if not flexi_seq.has_key(flexi_id) : # need to add entries to dictionaries holding packet number and time
          flexi_seq[flexi_id] = packet_seq # record last sequence number for this packet type
          seq_time[flexi_id] = packet_time+timeoffset[dpu_id] # record time of packet
          print 'First sequence number for DPU', (flexi_id >> 2), 'type', (flexi_id & 3), 'is', packet_seq, \
          ' time=', packet_time+timeoffset[dpu_id], bct_time_to_local(packet_time+timeoffset[dpu_id])
        elif ((flexi_seq[flexi_id]+1) % 2**14) != packet_seq : # sequence number increments incorrectly
          if (packet_seq == 1) : #JKB - comment out reset errors, error common. add counter?
            #print '***Reset for DPU', (flexi_id >> 2), 'type', (flexi_id & 3), \
      #  ' last=', flexi_seq[flexi_id], ' next=', packet_seq, \
       # ' time=', seq_time[flexi_id], bct_time_to_local(seq_time[flexi_id])
            timeoffset[dpu_id] = -1 # lose time information after offset
          else :
            placeholder=1 #JKB, comment out print statement, in lieu of PK loud changes
            #print '***Error in sequence numbers for DPU', (flexi_id >> 2), 'type', (flexi_id & 3), \
             # ' last=', flexi_seq[flexi_id], ' next=', packet_seq, \
             # ' time=', packet_time+timeoffset[dpu_id], bct_time_to_local(packet_time+timeoffset[dpu_id])
        if badcrc_flexi_id == flexi_id :
          placeholder=1 #JKB placeholder to keep check in place
          #print 'Packet following bad CRC. DPU=', dpu_id, ' packet type=', packet_type, ' seq=', packet_seq, \
          #   ' time=', packet_time+timeoffset[dpu_id], bct_time_to_local(packet_time+timeoffset[dpu_id])
         # store sequence number and time for this packet
        flexi_seq[flexi_id] = packet_seq # update packet sequence number
        seq_time[flexi_id] = packet_time+timeoffset[dpu_id] # update packet time
        tmp_time = packet_time+timeoffset[dpu_id]
        if packet_type == 3 :
          nhp += 1 # another housekeeping packet
	  try:
          	crc_ratio = float(nbadcrc)/float(nsp+nhp+nbadcrc)
          except:
		crc_ratio=0.0     
        elif packet_type == 2 :	
          tg=''.join(str(x) for x in tm[i+26:i+38+length]) #first part of unique tag is the packet interior hashed, with BCT header stripped (also sync). I don't trust the headers.
          hsh=hashlib.md5(tg) #JKB 11/19/18 
          tag=hsh.hexdigest()
          nsp += 1 # another science packet
          t = evtdata.process_packet(tm[(i+38):(i+38+length)], taitime, dpu_id, packet_time, timeoffset, packet_seq, tag, dbdir, datadir)
          nempa,nampa,ncmpa=t
          nemp+=nempa
          ncmp+=ncmpa
          namp+=nampa
	  try:
          	crc_ratio = float(nbadcrc)/float(nsp+nhp+nbadcrc)
          except:
		crc_ratio=0.0  

      else:
        badcrc_flexi_id = flexi_id # record which tm source had bad CRC
        nbadcrc += 1
	try:
        	crc_ratio = float(nbadcrc)/float(nsp+nhp+nbadcrc)
        except:
		crc_ratio=0.0  
        #print '***Bad CRC!  DPU=', dpu_id, ' packet type=', packet_type, ' seq=', packet_seq, \
        # ' previous seq=', flexi_seq[flexi_id], ' i=', i, ' time=', packet_time+timeoffset[dpu_id] #JKB com ment out error, too common, 10/25/18 #this doesnt work in this version.
        if (i+38+length > filelen) : print 'Bad CRC is at end of telemetry stream.'
      i += length+16

    else: #sync pattern not found, move on to next byte
        #print 'No sync pattern detected! check code/packets!'
        i+= 1
  print 'Number of bytes of telemetry = ', i

  for i in flexi_seq.keys() :
    try:
      print 'Last sequence number for DPU', (i >> 2), ' type ', (i & 3), ' is ', flexi_seq[i], \
            ' at time ', seq_time[flexi_id], bct_time_to_local(seq_time[flexi_id])
    except:
      print 'flexi id error - bad CRC?'
  if (nbadcrc > 0):
    print 'Found bad CRC(s)!', nbadcrc
  else :
    print 'No bad CRCs.'
  print 'Good Transport Frames: ', ntm#-hashdupe
  print 'Housekeeping packets: ', nhp
  print 'Science packets: ', nsp
  print 'Event data minipackets: ', nemp
  print 'Ancillary data minipackets: ', namp
  print 'Counter data minipackets: ', ncmp
  #print 'Duplicate packets: ', hashdupe
  return


def process_tmfiles(dbdir, datadir, filename, out=None, loud=False) :
# searches for FLEXI packets in a telemetry file and checks CRC and sequence numbers
# extracts housekeeping packets and writes the HK data to a FITS file
# datadir is directory where data is located
# filename is name of telemetry file
# if filename is empty [], processes all .bin files in datadir
# by default, FITS file has extension .hk replacing .bin
# if a different FITS filename is  extension is desired, set out = <FITS file name>
# set loud=True if you want verbose output

  # definition of housekeeing items
  # each element is [name, location, size, conversion]
  # where name is a string that is used for the FITS column name
  # location is the byte offset in the HK record
  # size = number of bits, 8 = one byte, 12 = two bytes, 16 = two bytes
  # conversion is either empty, in which case no conversion is done
  #   or a list [[a1, b1], [a2, b2], [a3, b3]]
  # value = an*raw+bn where n = unit number
  # calibrations for baseplate and SDD temperature sensors are from
  # Anna's file Flight temp avgCalib.ods from 2 Aug 2017

#jesse stripped out housekeeping stuff

  global crc_ratio, all_tags, all_dpu_id, all_etime, all_pulse, all_ptime, pt54, pt38, pt14, offsets14, offsets38, offsets54
  all_ptime=[]
  all_dpu_id =[]
  all_etime = []
  all_tags = []
  all_pulse=[]
  pt38=[]
  pt14=[]
  pt54=[]
  offsets14=[]
  offsets54=[]
  offsets38=[]
  crc_ratio=0.0
  # set up object to process and store data from science/event packets
  evtdata = EVTdata()

  fn = datadir+filename #list style processing was obsolete. JKB 5/20/19 edit.
  print 'Opening telemetry file ', fn
  tm = bytearray(os.path.getsize(fn))
  tm_file = open(fn, 'rb')
  tm_file.readinto(tm)
  process_tm(tm, filename, evtdata, dbdir, datadir, loud=loud)
  print

  #write database
  #print 'Writing data to science.db'
  if crc_ratio < 0.03:
    	write_db(dbdir, datadir)
  else:
	print "End-of-file write aborted: "+str(100*crc_ratio)+" percent CRC error rate in file."
  print 'completed file at: ', datetime.now()
  print

def proc_sci(dbdir,datadir):
    os.chdir(dbdir)
    logf=open('binlog.txt','r')
    processed=logf.readlines()
    logf.close()
    pro=[]
    os.chdir(datadir)
    extension = 'bin'
    result = [i for i in glob.glob('*.{}'.format(extension))]
    file_names=[]
    for x in range(len(result)):
            if result[x]+'\n' not in processed:
                processed.append(result[x])
                #pro.append(result[x])
                file_names.append(result[x])#end JKB edit

    name_len = len(file_names) #is this section needed now? --JKB
    for i in range(len(file_names)):
        file_name = file_names[i]
        file_name = file_name[0:-4] #JKB 5/20/19 - stripped out unused file extension if statements and checks
        out = None
        loud = False
        filename = file_name+'.bin'
	pro.append(filename)
        process_tmfiles(dbdir, datadir, filename)
    print 'new bin files:'
    print pro
    os.chdir(dbdir)
    logf4=open('binlog.txt','a')
    for indx in range(len(pro)):
      logf4.write(pro[indx]+'\n')
    logf4.close()
    

#if __name__ == '__main__':
logn=date.today()
logn2="logs/sci-2.2-"+str(logn)+".txt"
sys.stdout=open(logn2,"w")
datadir='/home/bct_halosat/payload/' #bin file directory
#datadir='/home/data/' #bin file manual directory
print 'Start time: ',datetime.now()
dbdir='/home/data/' #database directory
#backdir='/home/data/db_backups/' #DB backups directory OLD
backdir='/media/data/Elements/db_backups/' #new backup directory on external HDD
#create_science_db(dbdir)
day=date.today().weekday()
if day == 2: #wednesday = backup
	day2 = 'wed'
	backup=backdir+'science_'+day2+'.db'
	shutil.copyfile('science.db',backup)
	print 'Database backed up: '+backup+' at ',datetime.now()
proc_sci(dbdir,datadir)
print 'Processing complete at'
print datetime.now()
