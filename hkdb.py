'''
Routines to process ancillary data and write them to an SQLite database.
The ancillary data includes the TAI time, the orbit position, the orbit velocity,
the Attitude Quaternion, and an Attitude valid flag.

If the database file does not already exist, create it by running make_spacecraft_db().
Everytime new data come in from BCT, run process_tmfiles(datadir, filename)
where datadir is the directory with the telemetry files and filename is a list
of the telemetry files to be added.  See test1() for an example.


P. Kaaret 2018-08-24 to 2018-08-29
J. Bluem 2018-08-29 to 2019-09-15
Based of functions for minipacket data extraction by R. McCurdy 2017-02-22
and P. Kaaret 2017-03-08 to 2017-10/18.
'''

#J. Bluem, 10/23/2018 - cleaned up log text file stuff, replaced with print statements
#D. LaRocca 12/20/2018 - updated line 488 with Corrected X-ray Boresight wrt Body
#J. Bluem, 09/05/19 - version 2.0. Renamed fillDB_hk_anc as hkdb. Changed time offset scheme to store offsets until end of file. Corrects error with packet sequence breaks not deleting old offset. Also rewrote and cleaned code. Added duplication check.

import matplotlib.pyplot as plt
import os
from numpy import array, zeros, where, arange, full, histogram, mean, unique, sort
from numpy import sqrt, pi, arctan2, ndarray
import astropy.io.fits as pyfits
from datetime import datetime, timedelta, date
from pytz import timezone, utc
#from os import listdir
from sys import argv
import ctypes, struct
import sqlite3
import csv
import glob
import astropy.time
import pandas as pd
from quaternion import Quaternion
import sys
import hashlib

def eci2radec(eci):
  """
  Convert from ECI vector(s) to RA, Dec.  The input ``eci`` value
  can be an array of 3-vectors having shape (3,N) in which case
  the output RA, Dec will be arrays of length N.
  :param eci: ECI as 3-vector or (3,N) array
  :rtype: list ra, dec (degrees)
  """
  ra  = (180/pi)*arctan2(eci[1], eci[0])
  dec = (180/pi)*arctan2(eci[2], sqrt(eci[1]**2 + eci[0]**2))
  ok = ra < 0
  if isinstance(ok, ndarray):
    ra[ok] += 360
  elif ok:
    ra += 360
  return ra, dec

def tle_sorter(dbdir, tledir, dbfile='housekeeping.db'):
    path1 = dbdir
    os.chdir(path1)
    tlog=['TLE_Logs.txt'] #we dont want to run this file
    conn = sqlite3.connect(dbfile) #connect, read out list of files already run for TLEs
    c = conn.cursor()
    df=pd.read_sql_query('select TLE from tlelog',conn) #generate processed log for code to use
    prcd=df.TLE.values.tolist() #find previously run TLEs
    proc=tlog+prcd #merge for full set of files to NOT run
    path3 = tledir
    extension = 'txt'
    os.chdir(path3)
    reslt = [i for i in glob.glob('*.{}'.format(extension))] #find all TLE files.
    a=[]
    p=[] #these are newly processed files that will be written to the DB tlelog table
    timey=[]
    for x in range(len(reslt)):
        with open(reslt[x]) as csvfile:
            if reslt[x] not in proc: #new TLE, process
                TLEl=[]
                proc.append(reslt[x])
                p.append(reslt[x])
                reader = csv.reader(csvfile)
                for row in reader:
                    TLEl.append(row)
                    #lngt.append('tle')
                b=TLEl[0][0] + '\n' + TLEl[1][0] + '\n' + TLEl[2][0] #this conbtains the full TLE file data in the same multiline format
                a.append(b)
                time1=reslt[x][18:37] #time generated from file name, reformat for astropy
                yr=time1[0:4]
                mo=time1[5:7]
                dy=time1[8:10]
                hr=time1[11:13]
                mn=time1[14:16]
                sc=time1[17:19]
                tsr = str(yr) + '-' + str(mo) + '-' + str(dy) + 'T' + str(hr) + ':' + str(mn) + ':' + str(sc)
                t2 = astropy.time.Time(tsr)
                t2.format = 'unix'
                t=float(str(t2))
                t3=t+37.0-946684800.0 #adjust for epoch
                timey.append(t3)
    os.chdir(path1)
    #write timestamp and TLE to database, and the list of new TLE files processed
    c.executemany("""INSERT INTO tle (TIME, TLE) VALUES (?,?)""", zip(timey,a))
    c.executemany("""INSERT INTO tlelog (TLE) VALUES (?)""", zip(p))
    conn.commit()
    conn.close()
    print('new TLEs run:')
    print(p)
    print('new rows added:')
    print(len(timey))

def bct_time_to_local(event_time):
  # convert BCT times to unix times then to Central US time
  # BCT time is seconds since Epoch 2000-01-01 TAI time (GPS time)
  epoch_linux = datetime(1970, 1, 1)   # reference for POSIX epoch
  epoch_linux = utc.localize(epoch_linux)   # POSIX localized to UTC
  epoch_bct = datetime(2000, 1, 1)    # reference epoch yr = 2000.0 for BCT EDU
  epoch_bct = utc.localize(epoch_bct)   # epoch localized to UTC
  leapseconds = 37.0 # GPS time is offset from UTC time because of leap seconds
  # create datetime object from event_time [sec]
  time_delta = timedelta(seconds=event_time-leapseconds)
  true_time = epoch_bct + time_delta # get event time in UTC date:time
  # get seconds since POSIX for event_time
  true_time_unix = (true_time - epoch_linux).total_seconds()
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
  if (test_crc == good_crc):
    return True
  else:
    return False

class HKdata(object):
# class to accumulate housekeeping (HK) data as one reads through a file

  def __init__(self, db): # initialization routine
  # create a housekeeping data object
    self.db = db # save the database connection
    # list of HK data elements
    # each element is [name, location, size, conversion] where
    # name is a string that is used for the FITS column name
    # location is the byte offset in the HK record
    # size = number of bits, 8 = one byte, 12 = two bytes, 16 = two bytes
    # conversion is either empty, in which case no conversion is done
    #   or a list [[a1, b1], [a2, b2], [a3, b3]]
    # value = an*raw+bn where n = unit number
    # Note that -5V monitor is hard-coded because it depends on 2 readings
    # calibrations for baseplate and SDD temperature sensors are from
    # Anna's file Flight temp avgCalib.ods from 2 Aug 2017
    # updated for the replacement of flight 3 analog board with flight 4
    # 'TYPE1CNT', 0, 16, 'Command Type 1 Count', []
    # 'FLEXIINF', 6,  8, 'FLEXI command index not found', []
    # 'FLEXICNT', 8, 16, 'FLEXI instrument command counter', []
    # 'LRS_PCNT', 28, 16, 'LRS Packet Count', []
    # 'HSK_PCNT', 30, 16, 'HSK Packet Count', []
    # 'TEC_PWM', 37, 8, 'PWM Setting for TEC', []
    # 'DPU_TEMP', 42, -16, 'DPU Temperature', [1.0/128.0, 0.0]
    # 'ADC_TEMP', 44, 12, 'ADC Temperature', [1/2.654, 25-820.0/2.654]
    # 'DAC_TEMP', 46, 12, 'DAC Temperature', [1/2.654, 25-820.0/2.654]
    # 'MON_P5V', 50, 12, '5.0V Monitor', [2.470*2.5/4096, 0.0]
    # 'MON_3P3V', 52, 12, '3.3V Monitor', [1.605*2.5/4096, 0.0]
    # 'SDD_TEMP', 54, 12, 'SDD Temperature', \
    #   [[-0.27242, 266.03500], [-0.27527, 268.68608], [-0.27069, 264.36962]]
    # 'MON_M5VR', 56, 12, '-5.0V Monitor (raw)', [(1+60.4/20)*2.5/4096, 0.0]
    # 'BPL_TEMP', 58, 12, 'Baseplate Temperature', \
    #   [[-0.27380, 279.13876], [-0.28265, 285.62364], [-0.27349, 277.93624]]
    # 'SDDHVMON', 62, 12, 'SDD HV Monitor', [-79.158*2.5/4096, -0.0321]
    # 'SDD0', 70, 12, 'SDD0 Discriminiator', [2.5/4096, 0.0]
    # 'SDD1', 72, 12, 'SDD1 Discriminiator', [2.5/4096, 0.0]
    # 'SDDHVSET', 78, 12, 'SDD HV Set', [-80*(29.4/39.4)*2.5/4096, -0.0321]

  def process_packet(self, tm, dpu_id, tag, hktime, hedrtime):
  # process a HK packet and write the data to the database
    # hktime is TAI time of HK packet
    # dpu_id is DPU that produced the packet
    kdpu = {14:0, 54:1, 38:2} # map DPU numbers into detector numbers
    k = kdpu[dpu_id] # detector number (0, 1, 2) add 1 for normal naming
    # decode data in the packet
    # 'PWM Setting for TEC' is at byte 37 and has 8 bits
    tec_pwm = tm[37]
    # 'FLEXI command index not found' is at byte 6 has 8 bits
    flexiinf = tm[6]
    # 'ADC Temperature' is at byte 44 and has 12 bits
    raw = ((tm[44] & 0x0F)<< 8) | (tm[44+1])
    c = [1/2.654, 25-820.0/2.654]
    adc_temp = c[0]*raw + c[1] # same conversion for all DPUs
    # 'DAC Temperature' is at byte 46 and has 12 bits
    raw = ((tm[46] & 0x0F)<< 8) | (tm[46+1])
    c = [1/2.654, 25-820.0/2.654]
    dac_temp = c[0]*raw + c[1] # same conversion for all DPUs
    # '5.0V Monitor' is at byte 50 and has 12 bits
    raw = ((tm[50] & 0x0F)<< 8) | (tm[50+1])
    c = [2.470*2.5/4096, 0.0]
    mon_p5v = c[0]*raw + c[1] # same conversion for all DPUs
    # '3.3V Monitor' is at byte 52 and has 12 bits
    raw = ((tm[52] & 0x0F)<< 8) | (tm[52+1])
    c = [1.605*2.5/4096, 0.0]
    mon_3p3v = c[0]*raw + c[1] # same conversion for all DPUs
    # '-5.0V Monitor (raw)' is at byte 52 and has 12 bits
    raw = ((tm[56] & 0x0F)<< 8) | (tm[56+1])
    c = [(1+60.4/20)*2.5/4096, 0.0]
    mon_m5vr = c[0]*raw + c[1] # same conversion for all DPUs
    # calculation of the -5V monitor requires both the -5V reading and the +3.3V value
    mon_m5v = mon_m5vr - 3.02*mon_3p3v
    # 'SDD HV Monitor' is at byte 62 and has 12 bits
    raw = ((tm[62] & 0x0F)<< 8) | (tm[62+1])
    c = [-79.158*2.5/4096, -0.0321]
    sddhvmon = c[0]*raw + c[1] # same conversion for all DPUs
    # 'SDD0 Discriminiator' is at byte 70 and has 12 bits
    raw = ((tm[70] & 0x0F)<< 8) | (tm[70+1])
    c = [2.5/4096, 0.0]
    sdd0 = c[0]*raw + c[1] # same conversion for all DPUs
    # 'SDD1 Discriminiator' is at byte 72 and has 12 bits
    raw = ((tm[72] & 0x0F)<< 8) | (tm[72+1])
    c = [2.5/4096, 0.0]
    sdd1 = c[0]*raw + c[1] # same conversion for all DPUs
    # 'SDD HV Set' is at byte 78 and has 12 bits
    raw = ((tm[78] & 0x0F)<< 8) | (tm[78+1])
    c = [-80*(29.4/39.4)*2.5/4096, -0.0321]
    sddhvset = c[0]*raw + c[1] # same conversion for all DPUs
    # 'SDD Temperature' is at byte 54 and has 12 bits
    raw = ((tm[54] & 0x0F)<< 8) | (tm[54+1])
    c = [[-0.27242, 266.03500], [-0.27527, 268.68608], [-0.27069, 264.36962]]
    sdd_temp = c[k][0]*raw + c[k][1] # do linear conversion appropriate for DPU
    # 'Baseplate Temperature' is at byte 58 has 12 bits
    raw = ((tm[58] & 0x0F)<< 8) | (tm[58+1])
    c = [[-0.27380, 279.13876], [-0.28265, 285.62364], [-0.27349, 277.93624]]
    bpl_temp = c[k][0]*raw + c[k][1] # do linear conversion appropriate for DPU
    # 'Command Type 1 Count' is at byte 0 and has 16 bits
    type1cnt = (tm[0]<< 8) | (tm[0+1] )
    # 'FLEXI instrument command counter' is at byte 8 and has 16 bits
    flexicnt = (tm[8]<< 8) | (tm[8+1] )
    # 'LRS Packet Count' is at byte 28 and has 16 bits
    lrs_pcnt = (tm[28]<< 8) | (tm[28+1] )
    # 'HSK Packet Count' is at byte 30 and has 16 bits
    hsk_pcnt = (tm[30]<< 8) | (tm[30+1] )
    # 'DPU Temperature' is at byte 42 has 16 bits with sign
    raw = (tm[42]<< 8) | (tm[42+1] )
    # if high bit is set, then the number is negative
    if (raw >= 32768) : raw = raw-65536
    c = [1.0/128.0, 0.0]
    dpu_temp = c[0]*raw + c[1] # same conversion for all DPUs
    HK_hktime.append(hktime)
    HK_dpu_id.append(dpu_id)
    HK_mon_3p3v.append(mon_3p3v)
    HK_mon_p5v.append(mon_p5v)
    HK_mon_m5v.append(mon_m5v)
    HK_sddhvmon.append(sddhvmon)
    HK_sdd_temp.append(sdd_temp)
    HK_bpl_temp.append(bpl_temp)
    HK_dpu_temp.append(dpu_temp)
    HK_adc_temp.append(adc_temp)
    HK_dac_temp.append(dac_temp)
    HK_tec_pwm.append(tec_pwm)
    HK_sdd0.append(sdd0)
    HK_sdd1.append(sdd1)
    HK_sddhvset.append(sddhvset)
    HK_type1cnt.append(type1cnt)
    HK_flexiinf.append(flexiinf)
    HK_flexicnt.append(flexicnt)
    HK_lrs_pcnt.append(lrs_pcnt)
    HK_hsk_pcnt.append(hsk_pcnt)
    HK_tag.append(tag)
    HK_hdr.append(hedrtime)
    #the above replaces the old line-by-line DB write. hktime is truncated, now, and offset calculated during the write step/funxn. 
    #header time (HK_hdr) serves as the link between truncated time (hktime) and offset. JKB SEPT 6 2019

  def HK_Write(self): #writes only rows which have time offsets
    ejects=0
    for x in range(len(HK_hktime)):
      try:
        dpu=str(HK_dpu_id[x])
        t=HK_hktime[x]+TOS[dpu][HK_hdr[x]]
        # insert a new row into the database
        # SQLite command
        c = '''insert or ignore into housekeeping
               (TIME, DPU_ID,
                MON_3P3V, MON_P5V, MON_M5V, SDDHVMON,
                SDD_TEMP, BPL_TEMP, DPU_TEMP, ADC_TEMP, DAC_TEMP,
                TEC_PWM, SDD0, SDD1, SDDHVSET,
                TYPE1CNT, FLEXIINF, FLEXICNT, LRS_PCNT, HSK_PCNT, TAG)
               values (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)'''
        # data to be inserted
        d = [(t, HK_dpu_id[x],
              HK_mon_3p3v[x], HK_mon_p5v[x], HK_mon_m5v[x], HK_sddhvmon[x],
              HK_sdd_temp[x], HK_bpl_temp[x], HK_dpu_temp[x], HK_adc_temp[x], HK_dac_temp[x],
              HK_tec_pwm[x], HK_sdd0[x], HK_sdd1[x], HK_sddhvset[x],
              HK_type1cnt[x], HK_flexiinf[x], HK_flexicnt[x], HK_lrs_pcnt[x], HK_hsk_pcnt[x], HK_tag[x])]
        self.db.executemany(c, d)
      except:
        ejects+=1
    print('Housekeeping packets removed for missing time offsets:',ejects)

class ANCdata(object):
  # Class to accumulate ancillary (ANC) data as one reads through a file
  # The ancillary data is in the low rate science (LRS) data, which is the
  # X-ray event data stream, in minipackets of type 12.

  def __init__(self, db): # initialization routine
    # create an ancillary data object
    self.db = db # save the database connection

  def process_packet(self, tm, dpu_id, tag, htime, f, packet_time, loud=1) :
    # process a science data packet looking for ancillary data packets
    # write the contents of each ancillary data packet to the database
    # calculate RA, DEC from the quaternions and write RA, DEC to the database
    # tm is the telemetry packet data starting with the first minipacket
    # dpu_id is the ID of the DPU that produced the packets
    # sys_time is the DPU time in the telemetry packet header
    # timeoffset is an array of offsets between DPU time and TAI time
    # The routine returns the number of event, ancillary, and counter minipackets.
    # loud 0 = nothing, 1 = very important errors, 2 = all errors, 4 = lots of stuff
    nemp, namp, ncmp = 0, 0, 0 # number of minipackets (event, ancillary, counter)
    decode_length = 0 # number of bytes decoded
    length = len(tm)
    j = 0
    while (j < length-1): # only look for minipackets in this frame
      # byte 0 top 4 bits are the mini packet type
      mtype = ((tm[j] & 0xF0) >> 4)
      # byte 0 bottom 4 bits and byte 1 are length
      mlength = ((tm[j] & 0x0F) << 8) | ((tm[j+1]) & 0xFF)
      if (mtype == 0) : # 0 means fill data, skip rest of packet
        return nemp, namp, ncmp
      elif (mlength == 0) :
        if (loud > 0) : print('!!! Error: minipacket length of zero')
        if (loud > 0) : print('mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j))
        break # kill while loop
      elif ((j+mlength) >= length) :
        if (loud > 0) : print('!!! Error: minipacket does not fit in packet')
        if (loud > 0) : print('mini type=', mtype, ' mlength=', mlength, ' index=', j, ' hex=', hex(j), ' length=', length)
        break # kill while loop
      elif (mtype == 2): # HaloSat X-ray event minipacket
        nemp += 1 # chalk up another event minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF) # mini packet time
        # byte 4 is segmentation and MSF
        if (tm[j+4] & 0x80) == 0x80 :
          if (loud > 0) : print('!!! Error: Data are of questionable quality, j='+str(j)+'='+hex(j))
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00): mlength += 9
        else :
          if (loud > 0) : print('!!! Error MSF = ', msf)
        # byte 5 is data packing 2=packed event data (4 bytes), 1=raw event data (7 bytes)
        # the previous line is incorrect
        if (loud > 3): print('Event minipacket time=', find_mp_time(mp_time, packet_time, 0), 'len=', mlength)
      elif (mtype == 12): # ancillary data minipacket
        namp += 1 # chalk up another ancillary minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF)
        # byte 4, 5 are segmentation and MSF
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00) : mlength += 9
        else :
          if (loud > 0) : print('!!! Error MSF = ', msf)
        if (loud >3): print('Ancillary data time=', find_mp_time(mp_time, packet_time, 0), 'len=', mlength)
        # bytes 8 to 8+54 are BCT data with 4 sync bytes removed
        # bytes 14-17 are 32-bit time, TAI for BCT, unix for Willy
        k = j+4 # use k so offset match Table 5 in HaloSat As Built document
        utime = (tm[k+10]<<24)+(tm[k+11]<<16)+(tm[k+12]<<8)+tm[k+13]
        # find TAI time in seconds
        tai_time = float(utime) + float(tm[k+14])*0.2
        # bytes 63-67 are command arrival time
        ctime = tm[j+63]*0.025+tm[j+64]+(tm[j+65]<<8)+(tm[j+66]<<16)+(tm[j+67]<<24)
        newtimeoffset = utime-ctime
        TOS[str(dpu_id)][htime] = newtimeoffset
        # save aspect and orbit information
        # Orbit position in ECEF, data is in 4-byte floats in units of km
        position_ecef1 = struct.unpack('f', tm[k+19:k+15:-1])[0]
        position_ecef2 = struct.unpack('f', tm[k+23:k+19:-1])[0]
        position_ecef3 = struct.unpack('f', tm[k+27:k+23:-1])[0]
        # Attitude quaternion in ECI J2000, data is in 4-byte floats
        q_eci1 = struct.unpack('f', tm[k+31:k+27:-1])[0]
        q_eci2 = struct.unpack('f', tm[k+35:k+31:-1])[0]
        q_eci3 = struct.unpack('f', tm[k+39:k+35:-1])[0]
        q_eci4 = struct.unpack('f', tm[k+43:k+39:-1])[0]
        # Orbit velocity in ECEF, data is in 4-byte floats in units of km/s
        velocity_ecef1 = struct.unpack('f', tm[k+47:k+43:-1])[0]
        velocity_ecef2 = struct.unpack('f', tm[k+51:k+47:-1])[0]
        velocity_ecef3 = struct.unpack('f', tm[k+55:k+51:-1])[0]
        # Attitude valid (0=no, 1=yes)
        att_valid = tm[k+56] #JKB 11-2022 - was j+56, should be k+56
        print(att_valid) #EDITCHECK
        # !!! should check BCT checksum
        # PEK !!! 2018-10-19 added RA, DEC and lat,lon calculations
        # calculate pointing in RA and DEC
        # make quaternion, note BCT has scaler in last position
        quat = Quaternion(array([q_eci4, q_eci1, q_eci2, q_eci3]))
        body_xray_boresight = \
          array([0.012294797179809335, 0.0, 0.9999244161246925])
        ECI_xray_boresight = quat.rotate(body_xray_boresight)
        ra, dec = eci2radec(ECI_xray_boresight)
        # calculate sat_lat and sat_lon
        p = sqrt(position_ecef1**2 + position_ecef2**2) # sqrt(x^2 +y^2)
        sat_lat = (180/pi)*arctan2(position_ecef3, p) # arctan(z/p)
        sat_lon = (180/pi)*arctan2(position_ecef2, position_ecef1) # arctan(y/x)
        # insert a new row into the database
        # SQLite command
        tag=tag+str(namp)
        c = '''insert or ignore into spacecraft
               (TIME, DPU_ID, POSITION1, POSITION2, POSITION3,
                VELOCITY1, VELOCITY2, VELOCITY3,
                QUATERNION1, QUATERNION2, QUATERNION3, QUATERNION4,
                ATT_VALID,
                RA, DEC, SAT_LAT, SAT_LON, SOURCEFILE, TAG) values
               (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)'''
        # data to be inserted
        d = [(tai_time, dpu_id, position_ecef1, position_ecef2, position_ecef3, \
               velocity_ecef1, velocity_ecef2, velocity_ecef3, \
               q_eci1, q_eci2, q_eci3, q_eci4, att_valid, \
               ra, dec, sat_lat, sat_lon, f, tag)]
        self.db.executemany(c, d)
        if (loud >3):
          print(taitime, position_ecef1, position_ecef2, position_ecef3, \
                sqrt(position_ecef1**2 + position_ecef2**2 + position_ecef3**2))
          print('  ', velocity_ecef1, velocity_ecef2, velocity_ecef3, \
                sqrt(velocity_ecef1**2 + velocity_ecef2**2 + velocity_ecef3**2))
          print('  ', q_eci1, q_eci2, q_eci3, q_eci4, \
                sqrt(q_eci1**2 + q_eci2**2 + q_eci3**2 + q_eci4**2))
      elif (mtype == 3): # HaloSat counter data
        ncmp += 1 # another counter minipacket
        # bytes 2, 3 are truncated time
        mp_time = ((tm[j+2]&0xFF)<<8) | (tm[j+3]&0xFF)
        # byte 4 is segmentation and MSF
        if (tm[j+4] & 0x80) == 0x80 :
          if (loud > 0) : print('!!! Error: data are of questionable quality, j='+str(j)+'='+hex(j))
        msf = (tm[j+4] >> 5) & 0x03
        if (msf == 0x00) : mlength += 9
        else :
          if (loud > 0) : print('!!! Error MSF = ', msf)
        if (loud >3): print('Counter minipacket mp_time = ', mp_time, ' packet_time=', packet_time, ' msf=', msf, ' mlength=', mlength)
      else : # some other minipacket type
        if (loud > 0) : print('!!! Unknown minipacket type', mtype, 'len=', mlength, '  at ', j)
      # number of bytes decoded in this packet
      decode_length += mlength
      #move pointer ahead by length of mini packet
      j += mlength
    if decode_length != length :
      if (loud > 3): print('!!! Not all data decoded sys_time=', packet_time, ' length=', length, ' decode_length=', decode_length)
    return nemp, namp, ncmp

  def ancdata(self):
  # return the dictionary with the accumulated HK data
    return self.d

def process_tm(f, tm, ancdata, hkdata, loud=0):
  # extract event minipackets from HaloSat telemetry files
  global TOS, HK_hktime, HK_dpu_id, HK_mon_3p3v, HK_mon_p5v, HK_mon_m5v, HK_sddhvmon, HK_sdd_temp, HK_bpl_temp, HK_dpu_temp, HK_adc_temp, HK_dac_temp, HK_tec_pwm, HK_sdd0, HK_sdd1, HK_sddhvset, HK_type1cnt, HK_flexiinf, HK_flexicnt, HK_lrs_pcnt, HK_hsk_pcnt, HK_tag, HK_hdr
  TOS={} #dix for all offs
  TOS['14']={} #time offset dix for DPU 14
  TOS['38']={} #same, 38
  TOS['54']={} #54
  HK_hktime=[]
  HK_dpu_id=[]
  HK_mon_3p3v=[]
  HK_mon_p5v=[]
  HK_mon_m5v=[]
  HK_sddhvmon=[]
  HK_sdd_temp=[]
  HK_bpl_temp=[]
  HK_dpu_temp=[]
  HK_adc_temp=[]
  HK_dac_temp=[]
  HK_tec_pwm=[]
  HK_sdd0=[]
  HK_sdd1=[]
  HK_sddhvset=[]
  HK_type1cnt=[]
  HK_flexiinf=[]
  HK_flexicnt=[]
  HK_lrs_pcnt=[]
  HK_hsk_pcnt=[]
  HK_tag=[]
  HK_hdr=[]
  filelen = len(tm) # number of bytes in file
  print('File length = ', filelen)
  i = 0 # pointer index
  ntm = 0 # number of FLEXI packets found
  nhp = 0 # keep track of number of housekeeping packets
  nsp = 0 # keep track of number of science packets
  nep = 0 # keep track of number of event data minipackets
  nap = 0 # keep track of number of ancillary data minipackets
  ncp = 0 # keep track of number of count data minipackets
  nbadcrc = 0 # keep track of bad CRC's
  flexi_seq = {}
  seq_time = {}
  crc_tabccitt = init_crcccitt_tab() #create CRC table
  badcrc_flexi_id = -1 # good CRC
  # go through file
  while (i < filelen):
    if ((tm[i]==0x35) and (tm[i+1]==0x2E) and (tm[i+2]==0xF8) and (tm[i+3]==0x53) and (tm[i+22] == 0xFA) and (tm[i+23] == 0xF3) and (tm[i+24] == 0x34) and (tm[i+25] == 0x03)): #merged both header/sync checks into one - JKB 4/27 - i now becomes i+22
      # good sync pattern, so extract the packet
      ntm += 1 # have a new telemetry packet
      crc = (tm[i+4+22]<<8) | tm[i+5+22] # crc is bytes 4 and 5
      packet_type = (tm[i+6+22] & 0xC0) >> 6 # packet type 0=panic, 2=science, 3=housekeeping
      packet_seq = ((tm[i+6+22] & 0x3F) << 8) | tm[i+7+22] # sequence number
      length = (tm[i+14+22]<<8) | tm[i+15+22] # record length, starts with first minipacket byte
      tg=''.join(str(x) for x in tm[i+26:i+38+length]) #first part of unique tag is the packet interior hashed, with BCT header stripped (also sync). I don't trust the headers.
      hsh=hashlib.md5(tg) #JKB 11/19/18 
      tag=hsh.hexdigest()
      # packet time is bytes 8, 9, 10, 11. LSB of 11 is quality flag
      utime = (tm[i+10]<<24)+(tm[i+11]<<16)+(tm[i+12]<<8)+(tm[i+13]<<0) #header time
      htime = str(utime)[0:6] #truncated header string for 1000 second intervals. Tracks which time offset to use.
      packet_time = ((tm[i+8+22]&0xFF)<<24) | ((tm[i+9+22]&0xFF)<<16) | ((tm[i+10+22]&0xFF)<<8) | ((tm[i+11+22]&0xFE))
      if ((tm[i+11+22]&0x01) == 1): # got a bad time flag
        bad_time = True
        if (loud>3) : print('Bad Time!')
      dpu_id = ((tm[i+12+22]&0xFC)>>2) # DPU ID is bits 7:2 of byte 12
      if (loud > 3) : print('DPU = ', dpu_id, ' packet type, seq = ', packet_type, packet_seq)
      epoch = ((tm[i+12+22]&0x03)<<8) | tm[i+13] # epoch is bits 1:0 of byte 12 and byte 13
      # check if the sequence number increments sequentially for each DPU/packet type
      flexi_id = (dpu_id << 2) | packet_type
      if not flexi_seq.has_key(flexi_id) : # need to add entries to dictionaries holding packet number and time
        flexi_seq[flexi_id] = packet_seq # record last sequence number for this packet type
      try:
        seq_time[flexi_id] = packet_time+TOS[str(dpu_id)][htime] # record time of packet
      except:
        seq_time[flexi_id] = packet_time #no offset exists
        if (loud > 3): print('First sequence number for DPU', (flexi_id >> 2), 'type', (flexi_id & 3), 'is', packet_seq)
      if badcrc_flexi_id == flexi_id :
        if (loud > 1): print('Packet following bad CRC. DPU=', dpu_id, ' packet type=', packet_type, ' seq=', packet_seq, \
              ' time=', packet_time+TOS[str(dpu_id)][htime], bct_time_to_local(packet_time+TOS[str(dpu_id)][htime]))
      # check the packet CRC
      if crc_check(crc_tabccitt, tm[i+6+22:i+16+22+length], crc):
        badcrc_flexi_id = -1 # good CRC
        # process telemetry packets JKB moved inside CRC check 11/13/18, added filename f parameter to packet processing for logging
        if packet_type == 2 :
          nsp += 1 # another science packet
          t = ancdata.process_packet(tm[(i+16+22):(i+16+22+length)], dpu_id, tag, htime, f, packet_time)
          nep, nap, ncp = nep+t[0], nap+t[1], ncp+t[2] # keep track of number of minipackets
        elif packet_type == 3 :
          nhp += 1 # another housekeeping packet
          hkdata.process_packet(tm[(i+16+22):(i+16+22+length)], dpu_id, tag, packet_time, htime)
      else :
        badcrc_flexi_id = flexi_id # record which tm source had bad CRC
        nbadcrc += 1
        if (loud > 0) : print('***Bad CRC!  DPU=', dpu_id, ' packet type=', packet_type, ' seq=', packet_seq, \
              ' previous seq=', flexi_seq[flexi_id], ' i=', i, ' time=', packet_time+TOS[str(dpu_id)][htime])
        if (i+16+length > filelen) : print('Bad CRC is at end of telemetry stream.')
      # store sequence number and time for this packet
      flexi_seq[flexi_id] = packet_seq # update packet sequence number
      try:
      	seq_time[flexi_id] = packet_time+TOS[str(dpu_id)][htime] # update packet time
      except:
        seq_time[flexi_id] = packet_time
      #JKB 11/13/18 removed packet processing here, now under CRC check
      i += length+16+22
    else: #sync pattern not found, move on to next byte
      i+= 1
  if (loud > 3): print('Number of bytes of telemetry = ', i)
  for i in flexi_seq.keys() :
    if (loud > 1): print('Last sequence number for DPU', (i >> 2), ' type ', (i & 3), ' is ', flexi_seq[i], \
          ' at time ', seq_time[flexi_id], bct_time_to_local(seq_time[flexi_id]))
  if (nbadcrc > 0):
    print('Found bad CRC(s)!', nbadcrc)
  else :
    if (loud >2): print('No bad CRCs.')
  print('Packets: housekeeping=', nhp, ' science=', nsp)
  print('Minipackets: event=', nep, ' ancillary=', nap, 'counter=', ncp)
  hkdata.HK_Write()
  return

def make_spacecraft_db(dbdir, dbfile='housekeeping.db') :
  """
  Create a new SQLite database for the ancillary/spacecraft data and
  the instrument housekeeping data.
  dbdir is directory where database is located.
  dbfile is the name of the database file, default is 'housekeeping.db'

  """
  # should check if database already exists os.path.isfile(dbname)
  # open database to store spacecraft data
  db = sqlite3.connect(dbfile)
  c = db.cursor() # make connection to database
  # create table with spacecraft data in database JKB 11/13/18 added source file
  c.execute('''CREATE TABLE spacecraft
               (TIME real, DPU_ID int,
                POSITION1 real, POSITION2 real, POSITION3 real,
                VELOCITY1 real, VELOCITY2 real, VELOCITY3 real,
                QUATERNION1 real, QUATERNION2 real, QUATERNION3 real, QUATERNION4 real,
                ATT_VALID int,
                RA real, DEC real, SAT_LAT real, SAT_LON real, SOURCEFILE, TAG primary key)
            ''')
  c.execute('''CREATE TABLE housekeeping
               (TIME real, DPU_ID int,
                MON_3P3V real, MON_P5V real, MON_M5V real, SDDHVMON real,
                SDD_TEMP real, BPL_TEMP real, DPU_TEMP real, ADC_TEMP real, DAC_TEMP real,
                TEC_PWM int, SDD0 real, SDD1 real, SDDHVSET real,
                TYPE1CNT int, FLEXIINF int, FLEXICNT int, LRS_PCNT int, HSK_PCNT int, TAG primary key)
            ''')
  c.execute('''CREATE TABLE tlelog
               (TLE)
            ''')
  c.execute('''CREATE TABLE binlog
               (BIN)
            ''')
  c.execute('''CREATE TABLE tle
               (TIME, TLE)
            ''')
  db.commit() # commit the changes
  db.close() # close the connection to the database

def process_tmfiles(tmdir, dbdir, tmfiles=[], dbfile='housekeeping.db', loud=0) :
  """
  Searches for FLEXI packets in a telemetry file.
  It extracts ancillary/spacecraft data and housekeeping packets,
  decodes the packets, and writes the information to a database.
  tmdir is directory where telemetry files located
  dbdir is directory where database is located.
  tmfiles is a list of telemetry files, if [] then all .bin files in datadir are processed.
  dbfile is the name of the database file, default is 'housekeeping.db'
  Set loud=number if you want verbose output
"""
  os.chdir(dbdir)
  db = sqlite3.connect(dbfile)  # open the database
  df = pd.read_sql_query('select BIN from binlog', db)
  processedbins = df.BIN.values.tolist() # read list of files already processed
  # create object to process and store ancillary information
  # pass the database connection to the object
  ancdata = ANCdata(db)
  # set up object to process and store data from HK packets
  # pass the database connection to the object
  hkdata = HKdata(db)
  # if filename is empty [], processes all .bin files in datadir
  if len(tmfiles) == 0 :
    tmfiles = os.listdir(tmdir)
  # go through the list of filename(s) and process them if we haven't already
  newproc = [] # list of new files processed in this run
  for f in tmfiles: # f has file name
    if f.endswith('.bin') : # process only .bin files
      if f not in processedbins:
        	processedbins.append(f) 
        	newproc.append(f) # add file to list of newly processed files
        	fn = tmdir+f # full file name with path
        	print('Opening telemetry file ', fn)
        	tm = bytearray(os.path.getsize(fn))
        	tm_file = open(fn, 'rb')
        	tm_file.readinto(tm)
        	process_tm(f,tm, ancdata, hkdata, loud=loud)#JKB 11/13/18 pass filename into processing for logging
        	print
  # add names of files that were just processed to the database
  #os.chdir(dbdir) #EDITCHECK 5 lines starting here
  #c = db.cursor() # make a cursor into the database
  #c.executemany("""INSERT INTO binlog (BIN) VALUES (?)""", zip(newproc))
  #db.commit() # commit the changes to the database
  #db.close() # close the connection to the database
  print('new .bin files run:')
  print(newproc)

logn=date.today() #gets today's timestamp, used for file name of log file
logn2="logs/hk-2.0-"+str(logn)+".txt"
sys.stdout=open(logn2,"w") #write print outs to the logfile
# directory with telemetry (.bin) files
tmdir = '/home/bct_halosat/payload/'
# directory with database
dbdir = '/home/data/'
# directory with tle
tledir = '/home/halosat/haloSat/TLE'
make_spacecraft_db(dbdir)
print(datetime.now())
tle_sorter(dbdir,tledir) #parse TLE files
print('TLE files complete')
print(datetime.now())
process_tmfiles2(tmdir, dbdir) #process telemetry
print('.bin files complete')
print(datetime.now())
