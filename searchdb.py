# import libraries
import sqlite3
import astropy.io.fits as pyfits
from datetime import datetime, timedelta
import pandas as pd
import os
import numpy as np
from astropy.io import fits
from numpy import zeros, pi, sqrt, arctan2, ndarray, cos, sin, arcsin
#from numpy import zeros, pi, sqrt, arctan2, array, degrees, radians, ndarray, cos, sin, arcsin, concatenate
#from quaternion import Quaternion
import sys
#from numpy import where
from astropy import units as u
from astropy.coordinates import SkyCoord

#REVISION 2

#version 1.0 // JKB 10/26/18 - stitched together my code with the 3 fits writers from PK.
#version 1.1 // 10/30/18 JKB added command line inputs and haversine condition, LaRocca added ECEF2ECI changes -adding ecef2eci function -gmst function inside of it -haversine function, Changes search using 'DML 10/30'
#version 1.2 // JKB 11/7/18 - added altsearch function for specialized searches - just enter target number as 0 (zero). Added callsearch function to import into other code.
#verison 1.3 // JKB 11/9/18 - added searchparams, which narrows the field to an appropriate RA/DEC box before haversine. Should remove outliers from haversine bugs, and optimize the code speed maybe? -needs a larger size to account for haversign being larger than you expect from drawing a box - added 1 degree to delta when pulling box because haversine distance is larger than a simple additive delta
#version 1.4 // JKB 11/12/18 - switched to determining GTIs by index sequences rather than 8 seconds intervals, as 8 sec intervals do not always, or even often, hold. Still use 8 sec time interval as a safety check to not equate time distant sequentially indexed intervals
#version 1.5 // JKB 12/12/18 - added time print outs when running code and getDate function
#version 1.6 // JKB 12/19/18 - removed 0 length intervals, added total seconds per interval print out.
#version 1.7 // JKB 1/9/19 - changed ra/dec box to strip over declination interval, pulling all RAs, to correct a bug at high RAs.
#version 1.8 // JKB 4/16/19 - added text printout of time intervals.
#Version 1.9 // JKB 5/4/19 - made major change for offsets being in DB. Functionality doesnt change from perspective of end-user. Added stacking option under hidden options. Added GTI minimal value as a parameter set by the user.
#VERSION 1.9 IS MAJOR REVISION 2 - new database scheme, batch replacement of software.
#Version 1.10 // JKB 6/6/19 - changed GTI text file to new table in .bus FITS.
#version 1.11 // JKB 6/18/19 - restructured EVT FITS writing for improved speed. Large lists/arrays erased after last used, less looping over large lists/arrays.
#Version 1.12 // JKB 6/21/19 - added forked path for EVT FITS - if large obs, data temporarily written to .txt to save mem space. Is better for >2 obs, break even for 2.
#Version 1.13 // JKB 7/31/19 - minor update. _uf changed to _raw for file names. Cleaned up and deleted unused code.
#version 1.14 // JKB 8/16/19 - minor update, added to priamry headers max position offset for observation search and minimum GTI selected.
#version 1.15 // JKB 8/21/19 - added try/except statements to finding time offsets. Fails due to corrupted data for North Polar Spur, but could also fail from CRC errors deleting the time offsets. Added counter.
#version 1.16 // JKB 8/27/19 - Moved totaltime count step down to not count short GTIs in tally. Split code to a sys argv version. Just add parameters after searchdb.py in the terminal window like this: python searchdb.py TargetNumber GTImin Delta - IE python searchdb.py 5 16 1.1. Will recognize precisely what you are asking, and dump readouts to a txt file.
#version 1.17 // JKB 8/28/19 - edited printouts. Some printouts supressed on screen but show in .txt if run without prompts using command line args.
#version 1.18 // JKB 9/19/19 - moved the proc_id execution outside the try statement. try statement only applies to setting parameters off the command line. This prevents crashes sending you to choose a target, which causes hangs in automated code.
#version 1.19 // JKB 9/19/19 - Added .att attitude file generation. Slight adjustment of proc_id placement to be outside of try/except command line args section, so if it excepts it is because of syntax and not because of a crash later in the code. tai_time_conv function added for proper syntax in .att headers.
#version 1.20 // JKB 11/11/19 - Reordered Quaternions in .att file from 'dabc' to 'abcd'. Should match standards for prefilter now. 
#version 1.21 // JKB 12/13/19 - .att timedel keyword set to 2.0 in primary att table, deleted from GTI table, minor adjustments to other headers per archive doc.
#version 1.22 // JKB 12/18/19 - .hk file times round to nearest half second to correct for jitter.
#version 1.23 // JKB 01/09/20 - further adjustments to fits headers, added ID type, pulled from the targets file, propagated through to final FITS.
#version 1.24 // JKB 01/22/20 - Consolidated RR branch with main branch. Adds functionality for time cuts from command line and optional command line secondary log files for running multiple targets, in order to track failure of individual fields. Correct bug in object/target name header. Trailing zeroes didn't appear in decimals, resulting in faulty indexing. Forced a cut at the +/- sign for declination with sequential extraction of the second set of 6 digits that way the decimals don't matter. Few header edits, like capitalization and such. Changed away from HALOSAT JXXX-XXX style names for objects with common names, use common names instead. "Comment" added for certain offsets.
#version 1.25 // JKB 01/30/20 - various edits to the .att headers.
#version 1.26 // JKB 02/06/20 - Call FITS tables and columns by names and not indexes. Removed previously added "comment" from FITS files. Minor edits to table values.
#cersion 1.27 // JKB 02/17/20 - minor tweak. Removed seconds from the HaloSat JXXXXXX names.
#version 1.28 // JKB 8/15/20 - rearranged try/except statements lines 1568-1573, for RR.
#version 2.0 // JKB 10/02/22 - Updated for Python 3. Fixed raw_input and print statements. Changed filename timestamp to be set on code start rather than on writing of each file. Added 32 seconds to DATE-OBS and DATE-END to correct for time issues.
#version 2.1 // JKB 10/02/22 - Changed ATT_VALID from extracted table value to integer 255. Table data is meaningless. Raw data stream seems to be missing the ATT_VALID data. 255 is new flag meaning "no info".

def callsearch(N,gtimin=64,start=0,end=10E15,delt=0.25): #callable search function for usage in outside code JKB 11/8/18
    path1='/oldhome/data/haloSat_targets.fits' #file path to haloSat_targets.fits
    dbpath1='/oldhome/data/housekeeping.db' #path to housekeeping database
    dbpath2='/oldhome/data/science.db' #path to science database
    ID,NAME,RA,DC,IDT=KITFITSO(path1)#pulls all RA/DEC from FITS
    try:
        dex=ID.index(N) #valid ID
        ra=RA[dex]
        dc=DC[dex]
        idt=IDT[dex]
        namu=NAME[dex]
        print("Observation target:", NAME[dex])
        print("Right ascension and declination:", ra,dc)
    except:
        print('Target ID number not found') #invalid ID
        return
    searchdb(namu,idt,N,dbpath2,ra,dc,dbpath1,gtimin,START=start,END=end,DELTA=delt)

def getDate(time): #JKB addition 12/12/18 addition
  epoch_date = pd.to_datetime('2000/01/01 00:00:00')
  time1 = time - 37.0
  date = epoch_date + timedelta(seconds=time1)
  return date

def altsearch(gtimin,path1,dbpath1,dbpath2,timtim):
    delt=input('Specify delta search range in RA/Dec (degrees):')
    DELTA=float(delt)
    ans=input('Select method: 1=list of targets, 2=custom time interval, 3=manual RA and DEC, 4=stacked observations:')
    if ans=='1':
        Nlista=input('Write list of targets, separated by commas, no spaces, no leading zeros:')
        Nlist=Nlista.split(',')
        START=0
        END=10E15
        for N in Nlist:
            N=int(N)
            ID,NAME,RA,DC,IDT=KITFITSO(path1)#pulls all RA/DEC from FITS
            try:
                dex=ID.index(N) #valid ID
                ra=RA[dex]
                dc=DC[dex]
                idt=IDT[dex]
                namu=NAME[dex]
                print("Observation target:", NAME[dex])
                print("Right ascension and declination:", ra,dc)
                searchdb(namu,idt,N,dbpath2,ra,dc,dbpath1,gtimin,START,END,DELTA)
            except:
                print('Target ID number not found:', N) #invalid ID
                #return
    elif ans=='2':
        N=input("What is your target ID number? (Do not include leading zeros):")
        N=int(N)
        START=input("What is the start of time interval in TAI seconds:")
        END=input("What is the end of time interval in TAI seconds:")
        ID,NAME,RA,DC,IDT=KITFITSO(path1)#pulls all RA/DEC from FITS
        try:
            dex=ID.index(N) #valid ID
            ra=RA[dex]
            dc=DC[dex]
            idt=IDT[dex]
            namu=NAME[dex]
            print("Observation target:", NAME[dex])
            print("Right ascension and declination:", ra,dc)
            searchdb(namu,idt,N,dbpath2,ra,dc,dbpath1,gtimin,START,END,DELTA)
        except:
            print('Target ID number not found') #invalid ID
            #return
    elif ans=='3':
        ra=input('Specify Right Ascension:')
        dc=input('Specify Declination:')
        N=9999
        namu='Custom'
        print('Searching...')
        idt='Custom RA/Dec' 
        searchdb(namu,idt,N,dbpath2,ra,dc,dbpath1,gtimin,START,END,DELTA)
    elif ans=='4':
        Nlista=input('Write list of targets, separated by commas, no spaces, no leading zeros:')
        Nlist=Nlista.split(',')
        START=0
        END=10E15
        print('running time interval (j2000):',START,END)
    	#searches database for observations corresponding to start and end time in TAI, RA and DEC in degrees/decimals, same for deltas
        valid=[]
        end=[]
        start=[]
        conn=sqlite3.connect(dbpath1)
        c=conn.cursor()
        for N in Nlist:
            N=int(N)
            ID,NAME,RA,DC,IDT=KITFITSO(path1)#pulls all RA/DEC from FITS
            try:
                dex=ID.index(N) #valid ID
            except:
                print('Target ID number not found:', N) #invalid ID
            RRA=RA[dex]
            rDC=DC[dex]
            idt='Stacked'
            print("Observation target:", NAME[dex])
            print("Right ascension and declination:", RRA,rDC)
            RDC=searchparams(RRA,rDC,DELTA)
            df=pd.read_sql_query('select * from spacecraft GROUP BY TIME having TIME > ? and TIME < ? ORDER BY TIME ', conn, params=(START,END))
            for i in df.index:                   
                for x in range(len(RDC)):
                    if df.DEC[i] >= RDC[x][0] and df.DEC[i] <= RDC[x][1]:
                        ra=df.RA[i]
                        dc=df.DEC[i]
                        ll=haversine(ra,dc,RRA,rDC) #three new lines for circles JKB 10/30/18
                        if ll <= DELTA:
                            valid.append(i)
            if len(valid) == 0:
                print('No data found for target '+str(N))

            try:
                ts=df.TIME.values[valid]
                ls=[]
                ls.append(ts[0])
                for x in range(len(valid)-1):
                    if valid[x]+1 == valid[x+1] and ts[x+1]<ts[x]+9: #9 second interval for assumed 8 second time skip - this isnt always true though.
                        ls.append(ts[x+1])
                    else:
                        start.append(ls[0])
                        end.append(ts[x])
                        ls=[ts[x+1]]
                start.append(ls[0])
                end.append(ts[len(ts)-1]) #end new code
            except:
                print('time filter error')
        print
        totaltime=0
        start2=[]
        end2=[]
        print('GTI intervals (start/end date, start/end TAI, total seconds):') #JKB 12/12/18 addition
        for x in range(len(start)):
                doggy=str(getDate(start[x]))
                kitty=str(getDate(end[x]))
                wolf=doggy[0:21]
                lion=kitty[0:21]
                print(wolf, lion, start[x], end[x], end[x]-start[x])
                if start[x]+gtimin>end[x]:
                    print("Interval removed for being too small.")
                else:
                    totaltime+=end[x]-start[x]
                    start2.append(start[x])
                    end2.append(end[x])
    print('Total observation time= ',totaltime,' seconds.')
    print
    conn.close()
    if totaltime==0:
        print("No good time intervals found.")
        return
    #timmy=datetime.now() #three lines to generate timestamp for file name
    #timothy=str(timmy)
    #timtim=timothy[0:4]+timothy[5:7]+timothy[8:10]
    n="%04d" % (N,) #adds leading zeros for filename, if nec
    file_name='HS'+str(n)+'_'+timtim+'_raw_stacked' #filename in HSnnnn_yyyymmdd_uf format
    fitshk=file_name+'.hk'
    fitssc=file_name+'.bus'
    fitsatt=file_name+'.att'
    fitsev=file_name+'.evt'
    hk2fits(dbpath1, fitshk, start2, end2, gtimin, DELTA)
    spacecraft2fits(dbpath1, fitssc, start2, end2, gtimin, DELTA) #disable
    att2fits(idt,dbpath1, fitsatt, start2, end2, gtimin, DELTA, n, totaltime, RRA, rDC)
    evt2fits(dbpath2, fitsev, start2, end2, gtimin, DELTA)

def tai_time_conv(event_time, reftime='UTC', refout='DB'):
    from datetime import datetime, timedelta
    from pytz import utc

    # convert BCT times to unix times then to Central US time
    # BCT EDU time is seconds since Epoch 2000-01-01 TAI time (GPS time)
    # epoch_linux = datetime(1970, 1, 1, 0, 0, 0)   # reference for POSIX epoch
    # epoch_linux = utc.localize(epoch_linux)   # POSIX localized to UTC
    epoch_bct = datetime(2000, 1, 1, 0, 0, 0)    # reference epoch yr = 2000.0 for BCT EDU
    epoch_bct = utc.localize(epoch_bct)   # epoch localized to UTC
    if (reftime == 'UTC'): #default is utc
        leapseconds = 37.0 # GPS time is offset from UTC time because of leap seconds
    elif (reftime == 'tai'): 
        leapseconds = 0.0   # want time to stay in TAI
    time_delta = timedelta(seconds=event_time-leapseconds) # create datetime object from event_time [sec]
    true_time = epoch_bct + time_delta # get event time in UTC date:time
    utc_true_time = true_time.astimezone(utc) # true time should already be in UTC, but just making sure...
    if (refout == ''):  #default is 'hea'
        out_time = utc_true_time.strftime('%Y-%m-%d %H:%M:%S')
    elif (refout == 'tru'):
        out_time = utc_true_time.strftime('%m/%d/%Y %H:%M:%S')
    elif (refout == 'DB'):
        out_time = utc_true_time.strftime('%Y-%m-%dT%H:%M:%S')
    return out_time


def KITFITSO(path): #Processes FITS to lists for parsing for RA/DEC
    targets = fits.open(path)
    tdat=targets[1].data #index 0 = ID, index 2,3 = RA,DEC
    targets.close()
    ID=[]
    NAME=tdat['Target_Name']
    RA=tdat['RA']
    DC=tdat['DEC']
    IDT=tdat['Type']
    for x in range(len(tdat)): #carve FITS into target IDs, right ascension, declination
        ID.append(tdat[x]['Target_ID'])
    return ID, NAME, RA, DC, IDT

def proc_ID(N,gtimin,path1,dbpath1,dbpath2,flag,delt=0,rrts=0,rrte=10E15,tmtm=00000000): #takes ID# as input, finds RA/DEC - 1st function, calls KITFITSO
    ID,NAME,RA,DC,IDT=KITFITSO(path1)#pulls all RA/DEC from FITS
    try:
        dex=ID.index(N) #valid ID
        ra=RA[dex]
        dc=DC[dex]
        idt=IDT[dex]
        namu=NAME[dex] 
        print("Observation target:", NAME[dex])
        print("HaloSat target ID number:", N)
        print("Right ascension and declination:", ra,dc)
        if flag == 1:
            timmy=datetime.now()
            print("Date processed:",timmy)   	
            print("GTI minimum:",gtimin,"seconds")
    except:
        print('Target ID number not found') #invalid ID
        return
    if delt == 0:
    	delt=input("Choose a delta angular distance for RA and dec, in degrees:")
    delt=float(delt)
    if flag == 1:
        print("Angular offset:",delt,"degrees")
    searchdb(namu,idt,N,dbpath2,ra,dc,dbpath1,gtimin,DELTA=delt,START=rrts,END=rrte,timtim=tmtm)

def searchparams(tra,tdc,delt): #takes in ra, dec of target, and delta, calculates valid strip by declination cutoffs.
    dcs=[]
    dcs.append([tdc-delt,tdc+delt])
    return dcs

def searchdb(Namu,IDt,N,dbpath2,RA,DEC,path,gtimin,START=0,END=10E15,DELTA=0.25,timtim=00000000):
    print('Time interval search range (j2000):',START,END)
    #searches database for observations corresponding to start and end time in TAI, RA and DEC in degrees/decimals, same for deltas
    valid=[]
    conn=sqlite3.connect(path)
    c=conn.cursor()
    RDC=searchparams(RA,DEC,DELTA)
    df=pd.read_sql_query('select * from spacecraft GROUP BY TIME having TIME > ? and TIME < ? ORDER BY TIME ', conn, params=(START,END))
    conn.close()
    for i in df.index: #this code can serve to check RA/DEC calcs, so i didnt delete it JKB
        for x in range(len(RDC)):
            if df.DEC[i] >= RDC[x][0] and df.DEC[i] <= RDC[x][1]:
                ra=df.RA[i]
                dc=df.DEC[i]
                ll=haversine(ra,dc,RA,DEC) #three new lines for circles JKB 10/30/18
                if ll <= DELTA:
                    valid.append(i)
    if len(valid) == 0:
        print('No data found')
        return
    #new GTI code here. check index rather than time stamp.
    ls=[]
    end=[]
    start=[]
    ts=df.TIME.values[valid]
    ls.append(ts[0])
    for x in range(len(valid)-1):
        if valid[x]+1 == valid[x+1] and ts[x+1]<ts[x]+9: #9 second interval for assumed 8 second time skip - this isnt always true though. How fix? 2 sec for 1001:
            ls.append(ts[x+1])
        else:
            start.append(ls[0])
            end.append(ts[x])
            ls=[ts[x+1]]
    start.append(ls[0])
    end.append(ts[len(ts)-1]) #end new code
    ts=0
    df=0
    valid=0
    print
    totaltime=0
    start2=[]
    end2=[]
    print('GTI intervals (start/end date, start/end TAI, total seconds):') #JKB 12/12/18 addition
    for x in range(len(start)):
        doggy=str(getDate(start[x]))
        kitty=str(getDate(end[x]))
        wolf=doggy[0:21]
        lion=kitty[0:21]
        print(wolf, lion, start[x], end[x], end[x]-start[x])
        if start[x]+gtimin>end[x]:
            print("Interval removed for being too small.")
        else:
          start2.append(start[x])
          end2.append(end[x])
          totaltime+=end[x]-start[x]
    print('Total observation time= ',totaltime,' seconds.')
    print
    start=0
    end=0
    if totaltime==0:
      print("No good time intervals found.")
      return
    #timmy=datetime.now() #three lines to generate timestamp for file name
    #timothy=str(timmy)
    #timtim=timothy[0:4]+timothy[5:7]+timothy[8:10]
    n="%04d" % (N,) #adds leading zeros for filename, if nec
    file_name='HS'+str(n)+'_'+timtim+'_raw' #filename in HSnnnn_yyyymmdd_uf format
    fitshk=file_name+'.hk'
    fitssc=file_name+'.bus'
    fitsev=file_name+'.evt'
    fitsatt=file_name+'.att'
    hk2fits(path, fitshk, start2, end2, gtimin, DELTA)
    spacecraft2fits(path, fitssc, start2, end2, gtimin, DELTA) #disable per RR
    att2fits(Namu, IDt, dbpath1, fitsatt, start2, end2, gtimin, DELTA, n, totaltime, RA, DEC)
    if totaltime > 28000: #large observation length, do text file data storage
    	evt2fitslrg(dbpath2, fitsev, start2, end2, gtimin, DELTA)
    else: #small, run with data in memory
    	evt2fits(dbpath2, fitsev, start2, end2, gtimin, DELTA)

# Routine to take instrument housekeeping data from database and write to FITS file.
# P. Kaaret 2018-10-23 to 2018-10-26

def hk2fits(dbname, fits_name, t0, t1, gtimin, DELTA, loud=0) :
  """
  Read from an SQLite database for instrument housekeeping data for HaloSat
  and write the data to a FITS file.
  dbname is name of database file, can include a full or relative path.
  fits_name is name of output FITS file, can include a full or relative path.
  t0 is a list/array of start times of intervals.
  t1 is a list/array of end times of intervals.
  Times are in TAI seconds since 2000-01-01T00:00:00 UTC per BCT's useage.
  loud : 0 for no printing, >= 1 for differing levels of printing
  """

  # read the data table from the database
  db = sqlite3.connect(dbname) # open database to store spacecraft data
  c = db.cursor() # make a cursor into database
  # execute SQL commands to select all rows in the specified time intervals
  # in the spacecraft data table
  d = [] # where the data will go
  for i in range(len(t0)) : # loop over the time intervals
    c.execute('SELECT * FROM housekeeping WHERE time BETWEEN ? and ? ORDER BY time', (t0[i], t1[i]))
    d1 = c.fetchall() # fetch all the rows into the list d1
    for r in d1 : d.append(r) # append each row to d
  db.close() # close the connection to the database
  #!!! include lines to remove duplicate entries
  # each row in d consists of a tuple of numbers with the order setup by
  # the command used to define the data table which is
  # TIME real, DPU_ID int,
  # MON_3P3V real, MON_P5V real, MON_M5V real, SDDHVMON real,
  # SDD_TEMP real, BPL_TEMP real, DPU_TEMP real, ADC_TEMP real, DAC_TEMP real,
  # TEC_PWM int, SDD0 real, SDD1 real, SDDHVSET real,
  # TYPE1CNT int, FLEXIINF int, FLEXICNT int, LRS_PCNT int, HSK_PCNT int
  # !!! it would be nice to do the extract using names for the columns
  # !!! figure out how to do this - seems that can be done only row by row

  #%% copy data into arrays
  # define and fill numpy arrays for the quantities in the data table
  n = len(d) # the length of d is the number of rows of data
  # define the numpy arrays
  tai_time, dpu_id = zeros(n), zeros(n, int) # time and DPU_ID
  # voltage monitors
  mon_3p3v, mon_p5v, mon_m5v, sddhvmon = zeros(n), zeros(n), zeros(n), zeros(n)
  # temperatures
  sdd_temp, bpl_temp, dpu_temp, adc_temp, dac_temp = zeros(n), zeros(n), zeros(n), zeros(n), zeros(n)
  # controls
  tec_pwm, sdd0, sdd1, sddhvset = zeros(n, int), zeros(n), zeros(n), zeros(n)
  # command counters
  type1cnt, flexiinf, flexicnt  = zeros(n, int), zeros(n, int), zeros(n, int)
  # packet counters
  lrs_pcnt, hsk_pcnt = zeros(n, int), zeros(n, int)
  # loop over d and write the values into the appropriate arrays
  for i in range(n) :
    stimen=float(str(d[i][0])[0:10]) #rounds to nearest half second. JKB 12/18/19. Corrects for HK time jitter.
    stimed=float(str(d[i][0])[10])/10.0
    stime=round(2.0*stimed)/2.0
    tai_time[i] = stimen+stime
    dpu_id[i] = d[i][1]
    # voltage monitors
    mon_3p3v[i] =  d[i][2]
    mon_p5v[i] = d[i][3]
    mon_m5v[i] = d[i][4]
    sddhvmon[i] = d[i][5]
    # temperatures
    sdd_temp[i] = d[i][6]
    bpl_temp[i] = d[i][7]
    dpu_temp[i] = d[i][8]
    adc_temp[i] = d[i][9]
    dac_temp[i] = d[i][10]
    # controls
    tec_pwm[i] = d[i][11]
    sdd0[i] = d[i][12]
    sdd1[i] = d[i][13]
    sddhvset[i] = d[i][14]
    # command counters
    #type1cnt[i] = d[i][15]
    #flexiinf[i] = d[i][16]
    flexicnt[i] = d[i][17]
    # packet counters
    lrs_pcnt[i] = d[i][18]
    hsk_pcnt[i] = d[i][19]
  #%% write the data in arrays out to a FITS file
  # write event data to a FITS file with name fits_name
  prihdr = pyfits.Header() # create header for FITS file
  prihdr['MISSION'] = 'HaloSat'
  # date and time of file creation
  prihdr['SYSTIME'] = (str(datetime.now()), 'FITS file creation time')
  prihdr['MINTIME'] = (min(tai_time), 'Earliest time for spacecraft data')
  prihdr['MAXTIME'] = (max(tai_time), 'Latest time for spacecraft data')
  prihdr['MIN_GTI'] = (gtimin, 'Minimal good time interval allowed')
  prihdr['MAX_OFF'] = (DELTA, 'Allowed pointing degree offset')
  # create primary HDU
  prihdu = pyfits.PrimaryHDU(header=prihdr)
  # create columns for FITS file
  c_time = pyfits.Column(name='TIME', format='D', unit='s', array=tai_time)
  c_dpuid = pyfits.Column(name='DPU_ID', format='I', unit='', array=dpu_id)
  c_mon_3p3v = pyfits.Column(name='MON_3P3V', format='D', unit='V', array=mon_3p3v)
  c_mon_p5v = pyfits.Column(name='MON_P5V', format='D', unit='V', array=mon_p5v)
  c_mon_m5v = pyfits.Column(name='MON_M5V', format='D', unit='V', array=mon_m5v)
  c_sddhvmon = pyfits.Column(name='SDDHVMON', format='D', unit='V', array=sddhvmon)
  c_sdd_temp = pyfits.Column(name='SDD_TEMP', format='D', unit='degree C', array=sdd_temp)
  c_bpl_temp = pyfits.Column(name='BPL_TEMP', format='D', unit='degree C', array=bpl_temp)
  c_dpu_temp = pyfits.Column(name='DPU_TEMP', format='D', unit='degree C', array=dpu_temp)
  c_adc_temp = pyfits.Column(name='ADC_TEMP', format='D', unit='degree C', array=adc_temp)
  c_dac_temp = pyfits.Column(name='DAC_TEMP', format='D', unit='degree C', array=dac_temp)
  c_tec_pwm = pyfits.Column(name='TEC_PWM', format='I', unit='percent', array=tec_pwm)
  c_sdd0 = pyfits.Column(name='SDD0', format='D', unit='V', array=sdd0)
  c_sdd1 = pyfits.Column(name='SDD1', format='D', unit='V', array=sdd1)
  c_sddhvset = pyfits.Column(name='SDDHVSET', format='D', unit='V', array=sddhvset)
  #c_type1cnt = pyfits.Column(name='TYPE1CNT', format='I', unit='counts', array=type1cnt)
  #c_flexiinf = pyfits.Column(name='FLEXIINF', format='I', unit='counts', array=flexiinf)
  c_flexicnt = pyfits.Column(name='FLEXICNT', format='I', unit='counts', array=flexicnt)
  c_lrs_pcnt = pyfits.Column(name='LRS_PCNT', format='I', unit='counts', array=lrs_pcnt)
  c_hsk_pcnt = pyfits.Column(name='HSK_PCNT', format='I', unit='counts', array=hsk_pcnt)
  # combine columns
  cols = pyfits.ColDefs([c_time, c_dpuid, c_mon_3p3v, c_mon_p5v, c_mon_m5v, c_sddhvmon, \
                         c_sdd_temp, c_bpl_temp, c_dpu_temp, c_adc_temp, c_dac_temp, \
                         c_tec_pwm, c_sdd0, c_sdd1, c_sddhvset, \
                         c_flexicnt, c_lrs_pcnt, c_hsk_pcnt])
                         # c_type1cnt, c_flexiinf, \
  # create binary table HDU
  tbhdu = pyfits.BinTableHDU.from_columns(cols)
  # add comments, note this depends on the order the columns are written
  tbhdu.header.comments['TTYPE1'] = 'Time in TAI seconds since 2000-01-01T00:00:00'
  tbhdu.header.comments['TTYPE2'] = 'Data processing unit that generated telemetry'
  tbhdu.header.comments['TTYPE3'] = 'Monitor of 3.3V from spacecraft'
  tbhdu.header.comments['TTYPE4'] = 'Monitor of +5V from internal converter'
  tbhdu.header.comments['TTYPE5'] = 'Monitor of -5V from internal converter'
  tbhdu.header.comments['TTYPE6'] = 'Monitor of high voltage from HVPS'
  tbhdu.header.comments['TTYPE7'] = 'SDD temperature'
  tbhdu.header.comments['TTYPE8'] = 'Detector baseplate temperature'
  tbhdu.header.comments['TTYPE9'] = 'DPU temperature'
  tbhdu.header.comments['TTYPE10'] = 'ADC temperature'
  tbhdu.header.comments['TTYPE11'] = 'DAC temperature'
  tbhdu.header.comments['TTYPE12'] = 'Thermoelectic cooler controller duty cycle'
  tbhdu.header.comments['TTYPE13'] = 'SDD discriminator 0 setting'
  tbhdu.header.comments['TTYPE14'] = 'SDD discriminator 0 setting'
  tbhdu.header.comments['TTYPE15'] = 'SDD HVPS set value'
  #tbhdu.header.comments['TTYPE16'] = 'Count of Type 1 commands'
  #tbhdu.header.comments['TTYPE17'] = 'Count of FLEXI INF'
  tbhdu.header.comments['TTYPE16'] = 'Count of FLEXI commands'
  tbhdu.header.comments['TTYPE17'] = 'Count of low-rate science packets'
  tbhdu.header.comments['TTYPE18'] = 'Count of housekeeping packets'

  # write header and table to FITS file
  thdulist = pyfits.HDUList([prihdu, tbhdu])
  thdulist.writeto(fits_name, overwrite=True)
  thdulist.close()

  if (loud > 2) :
    print('Wrote ', str(n), ' rows of data to ', fits_name)
    print('Covering times from ', min(tai_time), ' to ', max(tai_time))

# Routines to take spacecraft data from database and write to FITS file.
# P. Kaaret 2018-08-26 to 2018-10-26

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


def att2fits(namez,idT, dbname, fits_name, t0, t1, gtimin, DELTA, N, totaltime, rat, dct, loud=0) :
  #modification of spacecraft2fits by JKB sept 2019 to make .att files.
  """
  DML 10/30
  Read from an SQLite database for spacecraft data for HaloSat
  and write the data to a FITS file.
  dbname is name of database file, can include a full or relative path.
  fits_name is name of output FITS file, can include a full or relative path.
  t0 is a list/array of start times of intervals.
  t1 is a list/array of end times of intervals.
  Times are in TAI seconds since 2000-01-01T00:00:00 UTC per BCT's useage.
  loud : 0 for no printing, >= 1 for differing levels of printing
  """

  # read the data table from the database
  db = sqlite3.connect(dbname) # open database to store spacecraft data
  c = db.cursor() # make a cursor into database
  ftime=datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%S')
  # execute SQL commands to select all rows in the specified time intervals
  # in the spacecraft data table
  d = [] # where the data will go
  for i in range(len(t0)) : # loop over the time intervals
    c.execute('SELECT * FROM spacecraft WHERE time BETWEEN ? and ? ORDER BY time', (t0[i], t1[i]))
    d1 = c.fetchall() # fetch all the rows into the list d1
    for r in d1 : d.append(r) # append each row to d
  db.close() # close the connection to the database
  # each row in d consists of a tuple of numbers with the order setup by
  # the command used to define the data table which is
  # TIME real, DPU_ID int,
  # POSITION1 real, POSITION2 real, POSITION3 real,
  # VELOCITY1 real, VELOCITY2 real, VELOCITY3 real,
  # QUATERNION1 real, QUATERNION2 real, QUATERNION3 real, QUATERNION4 real
  # RA real, DEC real, SAT_LAT real, SAT_LON real
  # !!! it would be nice to do the extract using names for the columns
  # !!! figure out how to do this
  timechek=[]
  d2=[]
  idT=idT.upper() ##edit for all caps
  for row in d:
    stimen=float(str(row[0])[0:10])
    stimed=float(str(row[0])[10])/10.0
    stime=round(2.0*stimed)/2.0
    fintime = stimen+stime
    if fintime not in timechek: #filter rows with same time.
        timechek.append(fintime)
        d2.append(row)

  #%% define and fill numpy arrays for the quantities in the data table
  n = len(d2) # the length of d is the number of rows of data
  # define the numpy arrays
  #tai_time, dpu_id = zeros(n), zeros(n, int) # time and DPU_ID
  tai_time = zeros(n)  # time, DPU unused
  position_ecef = zeros((n,3))
  velocity_ecef = zeros((n,3))
  quaternion_eci = zeros((n,4))
  att_valid = zeros(n, int) # attitude valid flag
  ra, dec = zeros(n), zeros(n)
  sat_lat, sat_lon = zeros(n), zeros(n)
  nadir_angle = zeros(n)

  # loop over d and write the values into the appropriate arrays
  for i in range(n) :
    stimen=float(str(d2[i][0])[0:10])
    stimed=float(str(d2[i][0])[10])/10.0
    stime=round(2.0*stimed)/2.0
    tai_time[i] = stimen+stime
    #dpu_id[i] = d2[i][1]
    position_ecef[i][:] = d2[i][2:5]
    velocity_ecef[i][:] = d2[i][5:8]
    quaternion_eci[i][0] = d2[i][8] # x #BCT has scaler in last position
    quaternion_eci[i][1] = d2[i][9] # y vector of quaternion
    quaternion_eci[i][2] = d2[i][10] # z vector of quaternion
    quaternion_eci[i][3] = d2[i][11] # scalar of quaternion
    att_valid[i] = 255 #d2[i][12] JKB - data wrong. hardcore in 255 for unknown.
    ra[i] = d2[i][13]
    dec[i] = d2[i][14]
    sat_lat[i] = d2[i][15]
    sat_lon[i] = d2[i][16]
    
    #observation intervals written to arrays JKB 6/6/19
  colA, colB, colC, colD, colE = zeros(len(t0),'U24'),zeros(len(t0),'U24'),zeros(len(t0)),zeros(len(t0)),zeros(len(t0))
  for idx in range(len(t0)): #start date/time, end date/time, start TAI sec, end TAI sec, total TAI sec
        colA[idx]=(str(getDate(t0[idx])).replace(' ','T'))[0:21]
        colB[idx]=(str(getDate(t1[idx])).replace(' ','T'))[0:21]
        colC[idx]=t0[idx]
        colD[idx]=t1[idx]
        colE[idx]=t1[idx]-t0[idx] #end JKB edit

  eci_zenith=ecef2eci(position_ecef,tai_time)
  ra_zenith,dec_zenith = eci2radec(eci_zenith)
  nadir_angle = 180 - haversine(ra,dec,ra_zenith,dec_zenith)
  n=str(N) #obs id
  #%% write the data out to a FITS file
  # write event data to a FITS file with name fits_name
  N=int(N)
  #if N>354 and N<373:
    #comnam=namez.replace(' ','_') #not used JKB 2022
  if (N>12) and (N!=63) and ((N<344) or (N>354)):  #if not common name, use J style coordinate name
  	crd = SkyCoord(ra=rat*u.degree, dec=dct*u.degree, frame='icrs')
  	crd2 = crd.to_string('hmsdms')
  	crd3=crd2.split("+")
  	try:
          crd4=crd3[1] #plus dec
          crd5='+'+crd4[0:2]+crd4[3:5]#+crd4[6:8]
  	except:
          crd4=crd3[0].split("-")[1] #minus dec
          crd5='-'+crd4[0:2]+crd4[3:5]#+crd4[6:8]
  	namez = 'HaloSat J'+crd2[0:2]+crd2[3:5]+crd5#+crd2[6:8]+crd5 #removed seconds
  else:
    namez=namez.replace(' ','_') #replace space with underscore in common name

  prihdr = pyfits.Header() # create header for FITS file
  prihdr['TELESCOP'] = ('HALOSAT ', 'Telescope (mission) name')
  prihdr['INSTRUME'] = ('SDD     ', 'Instrument name')
  #prihdr['DATAMODE'] = ('PHOTON', 'Instrument datamode') #goes somewhere else maybe.
  prihdr['OBS_ID'] = (n+'01', 'Observation ID')
  prihdr['OBJECT'] = (namez, 'Object/Target name')
  prihdr['OBJTYPE'] = (idT, 'Object/Target type')
  prihdr['DATE-OBS'] = (tai_time_conv(min(tai_time)+32), 'Start date of observation')
  prihdr['DATE-END'] = (tai_time_conv(max(tai_time)+32), 'End date of observation')
  #prihdr['TSTART'] = (min(tai_time), '[s] time start')
  #prihdr['TSTOP'] = (max(tai_time), '[s] time stop')
  #prihdr['ONTIME'] = (totaltime, '[s] Observation time on target')
  prihdr['DATE'] = (ftime, 'FITS file creation time')
  #prihdr['MIN_GTI'] = (gtimin, 'Minimal good time interval allowed')
  #prihdr['MAX_OFF'] = (DELTA, 'Allowed pointing degree offset')
  #if N>354 and N<373:
	#prihdr['COMMENT'] = comnam
  # create primary HDU
  prihdu = pyfits.PrimaryHDU(header=prihdr)
  # create columns for FITS file
  c_time = pyfits.Column(name='TIME', format='D', unit='s', array=tai_time)
  #c_dpuid = pyfits.Column(name='DPU_ID', format='I', array=dpu_id)
  c_position = pyfits.Column(name='POSITION', format='3D', unit='km', array=position_ecef)
  c_velocity = pyfits.Column(name='VELOCITY', format='3D', unit='km/s', array=velocity_ecef)
  c_quaternion = pyfits.Column(name='QPARAM', format='4D', array=quaternion_eci)
  c_att_valid = pyfits.Column(name='ATT_VALID', format='I', array=att_valid)
  c_sat_lat = pyfits.Column(name='SAT_LAT', format='D', unit='deg', array=sat_lat)
  c_sat_lon = pyfits.Column(name='SAT_LON', format='D', unit='deg', array=sat_lon)
  c_ra = pyfits.Column(name='RA', format='D', unit='deg', array=ra)
  c_dec = pyfits.Column(name='DEC', format='D', unit='deg', array=dec)
  c_nadir_angle = pyfits.Column(name='NADIR_ANGLE', format='D', unit='deg', array=nadir_angle)
  cols = pyfits.ColDefs([c_time, c_position, c_velocity, c_quaternion, c_att_valid, \
                         c_sat_lat, c_sat_lon, c_ra, c_dec, c_nadir_angle])
  # create binary table HDU
  tbhdu = pyfits.BinTableHDU.from_columns(cols)
  # add comments, note this depends on the order the columns are written
  tbhdu.header.comments['TTYPE1'] = 'Time' #in TAI seconds since 2000-01-01T00:00:00'
  tbhdu.header.comments['TFORM1'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT1'] = 'physical unit of field'
  #tbhdu.header.comments['TTYPE2'] = 'Data processing unit that generated telemetry'
  #tbhdu.header.comments['TFORM2'] = 'data format of field: 2-byte INTEGER'
  tbhdu.header.comments['TTYPE2'] = 'ECEF position of satellite [X,Y,Z]'
  tbhdu.header.comments['TFORM2'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT2'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE3'] = 'ECEF velocity of satellite [vX,vY,vZ]'
  tbhdu.header.comments['TFORM3'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT3'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE4'] = 'ECI quaternion of satellite [X,Y,Z,Scalar]'
  tbhdu.header.comments['TFORM4'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TTYPE5'] = 'Attitude valid (0=no, 1=yes, 255=no info)'
  tbhdu.header.comments['TFORM5'] = 'data format of field' #: 2-byte INTEGER'
  tbhdu.header.comments['TTYPE6'] = 'Satellite latitude'
  tbhdu.header.comments['TFORM6'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT6'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE7'] = 'Satellite longitude'
  tbhdu.header.comments['TFORM7'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT7'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE8'] = 'Right Ascension of the Pointing'
  tbhdu.header.comments['TFORM8'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT8'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE9'] = 'Declination of the Pointing'
  tbhdu.header.comments['TFORM9'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT9'] = 'physical unit of field'
  tbhdu.header.comments['TTYPE10'] = 'Angular distance from pointing to nadir'
  tbhdu.header.comments['TFORM10'] = 'data format of field' #: 8-byte DOUBLE'
  tbhdu.header.comments['TUNIT10'] = 'physical unit of field'
  tbhdu.header['EXTNAME'] = 'ATTITUDE'
  tbhdu.header.comments['EXTNAME'] = 'Binary table extension name'
  tbhdu.header['HDUCLASS'] = 'OGIP'
  tbhdu.header.comments['HDUCLASS'] = 'Format conforms to OGIP/GSFC standards'
  tbhdu.header['HDUCLAS1'] = 'TEMPORALDATA'
  tbhdu.header.comments['HDUCLAS1'] = 'First class level'
  tbhdu.header['HDUCLAS2'] = 'ATTITUDE'
  tbhdu.header.comments['HDUCLAS2'] = 'Second class level'
  tbhdu.header['TELESCOP'] = 'HALOSAT'
  tbhdu.header.comments['TELESCOP'] = 'Telescope (mission) name'
  tbhdu.header['INSTRUME'] = 'SDD'
  tbhdu.header.comments['INSTRUME'] = 'Instrument name'
  tbhdu.header['OBSERVER'] = 'PHILIP KAARET'
  tbhdu.header.comments['OBSERVER'] = 'Principal Investigator'
  tbhdu.header['OBS_ID'] = n+'01'
  tbhdu.header.comments['OBS_ID'] = 'Observation ID'
  tbhdu.header['OBJECT'] = namez
  tbhdu.header.comments['OBJECT'] = 'Object/target name'
  #if N>354 and N<373:
	#tbhdu.header['COMMENT'] = comnam
  tbhdu.header['OBJTYPE'] = (idT, 'Object/target type')
  tbhdu.header['EQUINOX'] = 2000
  tbhdu.header.comments['EQUINOX'] = '[yr] Equinox of celestial coord system'
  tbhdu.header['RADECSYS'] = 'FK5'
  tbhdu.header.comments['RADECSYS'] = 'celestial coord system'
  tbhdu.header['RA_NOM'] = rat
  tbhdu.header.comments['RA_NOM'] = '[deg] R.A. of nominal aspect point [J2000]'
  tbhdu.header['DEC_NOM'] = dct
  tbhdu.header.comments['DEC_NOM'] = '[deg] Dec. of nominal aspect point [J2000]'
  tbhdu.header['RA_OBJ'] = rat
  tbhdu.header.comments['RA_OBJ'] = '[deg] Object Right ascension [J2000]'
  tbhdu.header['DEC_OBJ'] = dct
  tbhdu.header.comments['DEC_OBJ'] = '[deg] Object Declination [J2000]'
  tbhdu.header['TIMESYS'] = 'TT'
  tbhdu.header.comments['TIMESYS'] = 'Reference time system'
  tbhdu.header['MJDREFI'] = 51544
  tbhdu.header.comments['MJDREFI'] = '[d] MJD reference day (2000-01-01T00:00:00)'
  tbhdu.header['MJDREFF'] = 0.00074287037037037
  tbhdu.header.comments['MJDREFF'] = '[d] MJD reference (fraction of day)'
  tbhdu.header['TIMEREF'] = 'LOCAL'
  tbhdu.header.comments['TIMEREF'] = 'Reference Frame'
  tbhdu.header['TASSIGN'] = 'SATELLITE'
  tbhdu.header.comments['TASSIGN'] = 'Time assigned by clock'
  tbhdu.header['TIMEUNIT'] = 's'
  tbhdu.header.comments['TIMEUNIT'] = 'Time unit for timing header keyword'
  tbhdu.header['TIMEDEL'] = 2.0
  tbhdu.header.comments['TIMEDEL'] = '[s] Data time resolution.'
  tbhdu.header['TIMEZERO'] = 0.0
  tbhdu.header.comments['TIMEZERO'] = '[s] Time Zero'
  tbhdu.header['TIMEPIXR'] = 1.0
  tbhdu.header.comments['TIMEPIXR'] = 'Bin time beginning=0 middle=0.5 end=1'
  tbhdu.header['TIERRELA'] = 4.0E-06
  tbhdu.header.comments['TIERRELA'] = '[s/s] relative errors expressed as rate'
  tbhdu.header['TIERABSO'] = 1.0
  tbhdu.header.comments['TIERABSO'] = '[s] timing precision in seconds'
  tbhdu.header['TSTART'] = min(tai_time)
  tbhdu.header.comments['TSTART'] = '[s] Observation start time'
  tbhdu.header['TSTOP'] = max(tai_time)
  tbhdu.header.comments['TSTOP'] = '[s] Observation stop time'
  #tbhdu.header['ONTIME'] = (totaltime, '[s] Observation time on target')
  tbhdu.header['DATE-OBS'] = tai_time_conv(min(tai_time)+32)
  tbhdu.header.comments['DATE-OBS'] = 'Start date of observations'
  tbhdu.header['DATE-END'] = tai_time_conv(max(tai_time)+32)
  tbhdu.header.comments['DATE-END'] = 'End date of observations'
  tbhdu.header['CLOCKAPP'] = True
  tbhdu.header.comments['CLOCKAPP'] = 'Clock correction applied" (F/T)'
  #tbhdu.header['DEADAPP'] = False
  #tbhdu.header.comments['DEADAPP'] = 'Has deadtime been applied to data?'
  tbhdu.header['ORIGIN'] = 'UNIVERSITY OF IOWA'
  tbhdu.header.comments['ORIGIN'] = 'origin of fits file'
  tbhdu.header['TLM2FITS'] = ('db_20221002','Telemetry converter FITS version')
  tbhdu.header['PROCVER'] = 'hsuf_20221026'#_hscl20200131'
  tbhdu.header.comments['PROCVER'] = 'Processing script version number'
  tbhdu.header['SOFTVER'] = 'Hea_11apr2022_V6.30.1'
  tbhdu.header.comments['SOFTVER'] = 'Software version'
  tbhdu.header['CREATOR'] = 'db'
  tbhdu.header.comments['CREATOR'] = 'Software Creator of the file'
  tbhdu.header['CALDBVER'] = 'hs20200129'
  tbhdu.header.comments['CALDBVER'] = 'CALDB index version used'
  tbhdu.header['DATE'] = ftime
  tbhdu.header.comments['DATE'] = 'file creation date'# (YYYY-MM-DDThh:mm:ss UT)'

  #JKB 6/6/19 - GTI table writing
  c1 = pyfits.Column(name='START_DATE', format='24A', unit='', array=colA)
  c2 = pyfits.Column(name='END_DATE', format='24A', unit='', array=colB)
  c3 = pyfits.Column(name='START', format='D', unit='s', array=colC)
  c4 = pyfits.Column(name='STOP', format='D', unit='s', array=colD)
  c5 = pyfits.Column(name='TOTAL_TIME', format='D', unit='s', array=colE)
  oicols = pyfits.ColDefs([c1,c2,c3,c4,c5])
  oihdu = pyfits.BinTableHDU.from_columns(oicols)
  oihdu.header.comments['TTYPE1'] = 'Start date in UTC'
  oihdu.header.comments['TFORM1'] = 'data format of field'
  oihdu.header.comments['TTYPE2'] = 'Stop date in UTC'
  oihdu.header.comments['TFORM2'] = 'data format of field'
  oihdu.header.comments['TTYPE3'] = 'Start time'
  oihdu.header.comments['TFORM3'] = 'data format of field'
  oihdu.header.comments['TUNIT3'] = 'physical unit of field'
  oihdu.header.comments['TTYPE4'] = 'Stop time'
  oihdu.header.comments['TFORM4'] = 'data format of field'
  oihdu.header.comments['TUNIT4'] = 'physical unit of field'
  oihdu.header.comments['TTYPE5'] = 'Total time for this interval' #Time in TAI seconds since 2000-01-01T00:00:00'
  oihdu.header.comments['TFORM5'] = 'data format of field'
  oihdu.header.comments['TUNIT5'] = 'physical unit of field'
  oihdu.header['EXTNAME'] = 'GTI'
  oihdu.header.comments['EXTNAME'] = 'Binary table extension name'
  oihdu.header['HDUCLASS'] = 'OGIP'
  oihdu.header.comments['HDUCLASS'] = 'Format conforms to OGIP/GSFC standards'
  oihdu.header['HDUCLAS1'] = 'GTI'
  oihdu.header.comments['HDUCLAS1'] = 'First class level'
  oihdu.header['HDUCLAS2'] = 'ALL'
  oihdu.header.comments['HDUCLAS2'] = 'Second class level'
  oihdu.header['TELESCOP'] = 'HALOSAT'
  oihdu.header.comments['TELESCOP'] = 'Telescope (mission) name'
  oihdu.header['INSTRUME'] = 'SDD'
  oihdu.header.comments['INSTRUME'] = 'Instrument name'
  oihdu.header['OBSERVER'] = 'PHILIP KAARET'
  oihdu.header.comments['OBSERVER'] = 'Principal Investigator'
  oihdu.header['OBS_ID'] = n+'01'
  oihdu.header.comments['OBS_ID'] = 'Observation ID'
  #if N>354 and N<373:
	#oihdu.header['COMMENT'] = comnam
  oihdu.header['OBJECT'] = namez
  oihdu.header.comments['OBJECT'] = 'Object/target name'
  oihdu.header['OBJTYPE'] = (idT, 'Object/target type')
  oihdu.header['EQUINOX'] = 2000.0
  oihdu.header.comments['EQUINOX'] = '[yr] Equinox of celestial coord system'
  oihdu.header['RADECSYS'] = 'FK5'
  oihdu.header.comments['RADECSYS'] = 'celestial coord system'
  oihdu.header['RA_NOM'] = rat
  oihdu.header.comments['RA_NOM'] = '[deg] R.A. of nominal aspect point [J2000]'
  oihdu.header['DEC_NOM'] = dct
  oihdu.header.comments['DEC_NOM'] = '[deg] Dec. of nominal aspect point [J2000]'
  oihdu.header['RA_OBJ'] = rat
  oihdu.header.comments['RA_OBJ'] = '[deg] Object Right ascension [J2000]'
  oihdu.header['DEC_OBJ'] = dct
  oihdu.header.comments['DEC_OBJ'] = '[deg]Object Declination [J2000]'
  oihdu.header['TIMESYS'] = 'TT'
  oihdu.header.comments['TIMESYS'] = 'Reference time system'
  oihdu.header['MJDREFI'] = 51544
  oihdu.header.comments['MJDREFI'] = '[d] MJD reference day (2000-01-01T00:00:00)'
  oihdu.header['MJDREFF'] = 0.00074287037037037
  oihdu.header.comments['MJDREFF'] = '[d] MJD reference (fraction of day)'
  oihdu.header['TIMEREF'] = 'LOCAL'
  oihdu.header.comments['TIMEREF'] = 'Reference Frame'
  oihdu.header['TASSIGN'] = 'SATELLITE'
  oihdu.header.comments['TASSIGN'] = 'Time assigned by clock'
  oihdu.header['TIMEUNIT'] = 's'
  oihdu.header.comments['TIMEUNIT'] = 'Time unit for timing header keyword'
  oihdu.header['TIMEZERO'] = 0.0
  oihdu.header.comments['TIMEZERO'] = 'Time Zero'
  #oihdu.header['TIMEPIXR'] = 0
  #oihdu.header.comments['TIMEPIXR'] = 'Bin time beginning=0 middle=0.5 end=1'
  #oihdu.header['TIERRELA'] = 1.0E-8
  #oihdu.header.comments['TIERRELA'] = '[s/s] relative errors expressed as rate'
  #oihdu.header['TIERABSO'] = 1.0
  #oihdu.header.comments['TIERABSO'] = '[s] timing precision in seconds'
  oihdu.header['TSTART'] = min(tai_time)
  oihdu.header.comments['TSTART'] = '[s] Observation start time'
  oihdu.header['TSTOP'] = max(tai_time)
  oihdu.header.comments['TSTOP'] = '[s] Observation stop time'
  #oihdu.header['ONTIME'] = (totaltime, '[s] Observation time on target')
  oihdu.header['DATE-OBS'] = tai_time_conv(min(tai_time)+32)
  oihdu.header.comments['DATE-OBS'] = 'Start date of observations'
  oihdu.header['DATE-END'] = tai_time_conv(max(tai_time)+32)
  oihdu.header.comments['DATE-END'] = 'End date of observations'
  oihdu.header['CLOCKAPP'] = True
  oihdu.header.comments['CLOCKAPP'] = 'Clock correction applied? (F/T)'
  #oihdu.header['DEADAPP'] = False
  #oihdu.header.comments['DEADAPP'] = 'Has deadtime been applied to data?'
  oihdu.header['ORIGIN'] = 'UNIVERSITY OF IOWA'
  oihdu.header.comments['ORIGIN'] = 'origin of fits file'
  oihdu.header['TLM2FITS'] = ('db_20221002','Telemetry converter FITS version')
  oihdu.header['PROCVER'] = 'hsuf_20221026'#_hscl20200131'
  oihdu.header.comments['PROCVER'] = 'Processing script version number'
  oihdu.header['SOFTVER'] = 'Hea_11apr2022_V6.30.1'
  oihdu.header.comments['SOFTVER'] = 'Software version'
  oihdu.header.comments['SOFTVER'] = 'Software version'
  oihdu.header['CREATOR'] = 'db'
  oihdu.header.comments['CREATOR'] = 'Software Creator of the file'
  oihdu.header['CALDBVER'] = 'hs20190129'
  oihdu.header.comments['CALDBVER'] = 'CALDB index version used'
  oihdu.header['DATE'] = ftime
  oihdu.header.comments['DATE'] = 'file creation date'# (YYYY-MM-DDThh:mm:ss UT)'
  #end JKB edit  

  # write header and table to FITS file
  thdulist = pyfits.HDUList([prihdu, tbhdu, oihdu])
  thdulist.writeto(fits_name, overwrite=True)
  #thdulist.close()

  if (loud > 2) :
    print('Wrote ', str(n), ' rows of data to ', fits_name)
    print('Covering times from ', min(tai_time), ' to ', max(tai_time))


def spacecraft2fits(dbname, fits_name, t0, t1, gtimin, DELTA, loud=0) :
  """
  DML 10/30
  Read from an SQLite database for spacecraft data for HaloSat
  and write the data to a FITS file.
  dbname is name of database file, can include a full or relative path.
  fits_name is name of output FITS file, can include a full or relative path.
  t0 is a list/array of start times of intervals.
  t1 is a list/array of end times of intervals.
  Times are in TAI seconds since 2000-01-01T00:00:00 UTC per BCT's useage.
  loud : 0 for no printing, >= 1 for differing levels of printing
  """

  # read the data table from the database
  db = sqlite3.connect(dbname) # open database to store spacecraft data
  c = db.cursor() # make a cursor into database

  # execute SQL commands to select all rows in the specified time intervals
  # in the spacecraft data table
  d = [] # where the data will go
  for i in range(len(t0)) : # loop over the time intervals
    c.execute('SELECT * FROM spacecraft WHERE time BETWEEN ? and ? ORDER BY time', (t0[i], t1[i]))
    d1 = c.fetchall() # fetch all the rows into the list d1
    for r in d1 : d.append(r) # append each row to d
  db.close() # close the connection to the database
  # each row in d consists of a tuple of numbers with the order setup by
  # the command used to define the data table which is
  # TIME real, DPU_ID int,
  # POSITION1 real, POSITION2 real, POSITION3 real,
  # VELOCITY1 real, VELOCITY2 real, VELOCITY3 real,
  # QUATERNION1 real, QUATERNION2 real, QUATERNION3 real, QUATERNION4 real
  # RA real, DEC real, SAT_LAT real, SAT_LON real
  # !!! it would be nice to do the extract using names for the columns
  # !!! figure out how to do this


  #%% define and fill numpy arrays for the quantities in the data table
  n = len(d) # the length of d is the number of rows of data
  # define the numpy arrays
  tai_time, dpu_id = zeros(n), zeros(n, int) # time and DPU_ID
  position_ecef = zeros((n,3))
  velocity_ecef = zeros((n,3))
  quaternion_eci = zeros((n,4))
  att_valid = zeros(n, int) # attitude valid flag
  ra, dec = zeros(n), zeros(n)
  sat_lat, sat_lon = zeros(n), zeros(n)
  nadir_angle = zeros(n)

  # loop over d and write the values into the appropriate arrays
  for i in range(n) :
    tai_time[i] = d[i][0]
    dpu_id[i] = d[i][1]
    position_ecef[i][:] = d[i][2:5]
    velocity_ecef[i][:] = d[i][5:8]
    quaternion_eci[i][0] = d[i][11] # BCT has scaler in last position
    quaternion_eci[i][1] = d[i][8] # x vector of quaternion
    quaternion_eci[i][2] = d[i][9] # y vector of quaternion
    quaternion_eci[i][3] = d[i][10] # z vector of quaternion
    att_valid[i] = 255 #d[i][12] value is incorrect in raw data. hardcoded as 255 for indeterminate. JKB 12/7/22
    ra[i] = d[i][13]
    dec[i] = d[i][14]
    sat_lat[i] = d[i][15]
    sat_lon[i] = d[i][16]
    
    #observation intervals written to arrays JKB 6/6/19
  colA, colB, colC, colD, colE = zeros(len(t0),'U24'),zeros(len(t0),'U24'),zeros(len(t0)),zeros(len(t0)),zeros(len(t0))
  for idx in range(len(t0)): #start date/time, end date/time, start TAI sec, end TAI sec, total TAI sec
        colA[idx]=str(getDate(t0[idx]))
        colB[idx]=str(getDate(t1[idx]))
        colC[idx]=t0[idx]
        colD[idx]=t1[idx]
        colE[idx]=t1[idx]-t0[idx] #end JKB edit

  eci_zenith=ecef2eci(position_ecef,tai_time)
  ra_zenith,dec_zenith = eci2radec(eci_zenith)
  nadir_angle = 180 - haversine(ra,dec,ra_zenith,dec_zenith)

  #%% write the data out to a FITS file
  # write event data to a FITS file with name fits_name
  prihdr = pyfits.Header() # create header for FITS file
  prihdr['MISSION'] = 'HaloSat'
  # date and time of file creation
  prihdr['SYSTIME'] = (str(datetime.now()), 'FITS file creation time')
  prihdr['MINTIME'] = (min(tai_time), 'Earliest time for spacecraft data')
  prihdr['MAXTIME'] = (max(tai_time), 'Latest time for spacecraft data')
  prihdr['MIN_GTI'] = (gtimin, 'Minimal good time interval allowed')
  prihdr['MAX_OFF'] = (DELTA, 'Allowed pointing degree offset')
  # create primary HDU
  prihdu = pyfits.PrimaryHDU(header=prihdr)
  # create columns for FITS file
  c_time = pyfits.Column(name='TIME', format='D', unit='s', array=tai_time)
  c_dpuid = pyfits.Column(name='DPU_ID', format='I', array=dpu_id)
  c_position = pyfits.Column(name='POSITION', format='3D', unit='km', array=position_ecef)
  c_velocity = pyfits.Column(name='VELOCITY', format='3D', unit='km/s', array=velocity_ecef)
  c_quaternion = pyfits.Column(name='QUATERNION', format='4D', array=quaternion_eci)
  c_att_valid = pyfits.Column(name='ATT_VALID', format='I', array=att_valid)
  c_sat_lat = pyfits.Column(name='SAT_LAT', format='D', unit='deg', array=sat_lat)
  c_sat_lon = pyfits.Column(name='SAT_LON', format='D', unit='deg', array=sat_lon)
  c_ra = pyfits.Column(name='RA', format='D', unit='deg', array=ra)
  c_dec = pyfits.Column(name='DEC', format='D', unit='deg', array=dec)
  c_nadir_angle = pyfits.Column(name='NADIR_ANGLE', format='D', unit='deg', array=nadir_angle)
  cols = pyfits.ColDefs([c_time, c_dpuid, c_position, c_velocity, c_quaternion, c_att_valid, \
                         c_sat_lat, c_sat_lon, c_ra, c_dec, c_nadir_angle])
  # create binary table HDU
  tbhdu = pyfits.BinTableHDU.from_columns(cols)
  # add comments, note this depends on the order the columns are written
  tbhdu.header.comments['TTYPE1'] = 'Time in TAI seconds since 2000-01-01T00:00:00'
  tbhdu.header.comments['TTYPE2'] = 'Data processing unit that generated telemetry'
  tbhdu.header.comments['TTYPE3'] = 'ECEF position of satellite [X,Y,Z]'
  tbhdu.header.comments['TTYPE4'] = 'ECEF velocity of satellite [X,Y,Z]'
  tbhdu.header.comments['TTYPE5'] = 'ECI quaternion of satellite [Scalar,X,Y,Z]'
  tbhdu.header.comments['TTYPE6'] = 'Attitude valid (0=no, 1=yes, 255=no info)'
  tbhdu.header.comments['TTYPE7'] = 'Satellite sub-point latitude'
  tbhdu.header.comments['TTYPE8'] = 'Satellite sub-point longitude'
  tbhdu.header.comments['TTYPE9'] = 'Pointing - RA'
  tbhdu.header.comments['TTYPE10'] = 'Pointing - DEC'
  tbhdu.header.comments['TTYPE11'] = 'Angular distance from pointing to nadir'
  
  #JKB 6/6/19 - GTI table writing
  c1 = pyfits.Column(name='START_DATE', format='24A', unit='', array=colA)
  c2 = pyfits.Column(name='END_DATE', format='24A', unit='', array=colB)
  c3 = pyfits.Column(name='START_TIME', format='D', unit='s', array=colC)
  c4 = pyfits.Column(name='END_TIME', format='D', unit='s', array=colD)
  c5 = pyfits.Column(name='TOTAL_TIME', format='D', unit='s', array=colE)
  oicols = pyfits.ColDefs([c1,c2,c3,c4,c5])
  oihdu = pyfits.BinTableHDU.from_columns(oicols)
  oihdu.header.comments['TTYPE1'] = 'UTC time'
  oihdu.header.comments['TTYPE2'] = 'UTC time'
  oihdu.header.comments['TTYPE3'] = 'Time in TAI seconds since 2000-01-01T00:00:00'
  oihdu.header.comments['TTYPE4'] = 'Time in TAI seconds since 2000-01-01T00:00:00'
  oihdu.header.comments['TTYPE5'] = 'Time in TAI seconds since 2000-01-01T00:00:00'
  #end JKB edit  

  # write header and table to FITS file
  thdulist = pyfits.HDUList([prihdu, tbhdu, oihdu])
  thdulist.writeto(fits_name, overwrite=True)
  #thdulist.close()

  if (loud > 2) :
    print('Wrote ', str(n), ' rows of data to ', fits_name)
    print('Covering times from ', min(tai_time), ' to ', max(tai_time))

# Routine to take instrument event data from database and write to FITS file.
# P. Kaaret 2018-10-26 - heavily modified later by JKB

def evt2fitslrg(dbname, fits_name, t0, t1, gtimin, DELTA, pha_cut=[], loud=0) :
  """
  Read from an SQLite database for instrument event data for HaloSat
  and write the data to a FITS file.
  dbname is name of database file, can include a full or relative path.
  fits_name is name of output FITS file, can include a full or relative path.
  t0 is a list/array of start times of intervals.
  t1 is a list/array of end times of intervals.
  Times are in TAI seconds since 2000-01-01T00:00:00 UTC per BCT's useage.
  pha_cut is a list of lower and upper bounds on the PHA values for events
  written to the FITS file.  If empty, all events are written.  If one pair
  of numbers, then the same cuts are applied to all DPUs.  If three pairs
  of numbers, then each DPU gets its own cuts.
  loud : 0 for no printing, >= 1 for differing levels of printing
  """

  # information for conversion from PHA to PI
  # taken from Anna's !!!
  # !!! should really look this up in a database in case the conversion changes with time
  #print 'Starting event writing...'
  c1 = [0.5440, 0.5496, 0.5770] # coefficients for conversion of ADC channels to eV, DPUs 14, 54, 38
  c2 = [-30.5, -36.3, -34.6]    # E = C1*PHA + C2
  ebin = 0.01 # [keV] energy bin size for PI
  pi_unit = str(1000*ebin)+ 'eV'

  # read the data table from the database
  db = sqlite3.connect(dbname) # open database to store spacecraft data
  c = db.cursor() # make a cursor into database
  
  # execute SQL commands to select all rows in the specified time intervals
  # in the spacecraft data table
  offset14={}#Generate timeoffset dictionaries
  offset38={}
  offset54={}
  t00=[]
  t11=[]
  #%
  for i in range(len(t0)) : # loop over the time intervals, truncate to match DB stored values, and merge if intervals would overlap in widened DB search
    val=str(t0[i])
    val=val[0:6]
    val=int(val)
    val2=str(t1[i])
    val2=val2[0:6]
    val2=int(val2)+1
    if len(t00)>0 and val<=t11[len(t11)-1]:
      t11[len(t11)-1]=val2
    else:
      t00.append(val) #at this point, we've converted (roughly) event times back into header times to use to search the DB
      t11.append(val2)
  for i in range(len(t00)):
    c.execute('SELECT * FROM offsets14 WHERE pkt_time_14 BETWEEN ? and ?', (t00[i], t11[i]))
    offs1=c.fetchall()
    for x in range(len(offs1)):
          offset14[offs1[x][1]]=offs1[x][0] #use header time as dict key to find offset, dict for each DPU
    c.execute('SELECT * FROM offsets38 WHERE pkt_time_38 BETWEEN ? and ?', (t00[i], t11[i]))
    offs2=c.fetchall()
    for x in range(len(offs2)):
          offset38[offs2[x][1]]=offs2[x][0]
    c.execute('SELECT * FROM offsets54 WHERE pkt_time_54 BETWEEN ? and ?', (t00[i], t11[i]))
    offs3=c.fetchall()
    for x in range(len(offs3)):
          offset54[offs3[x][1]]=offs3[x][0]
  offs1=0 #clear as much mem as possible
  offs2=0
  offs3=0
  tempftime=datetime.now()
  T=str(tempftime)
  tempdpu="tempdpu"+T+".txt"
  temppha="temppha"+T+".txt"
  temptime="temptime"+T+".txt"
  temppi="temppi"+T+".txt"
  dputxt = open(tempdpu,"a") #temporary txts to reduce memory burden
  phatxt = open(temppha,"a")
  timtxt = open(temptime,"a")
  pitxt = open(temppi,"a")
  d = [] # where the data will go
  #print 'fetching data from DB'
  #print "Offsets complete: ", datetime.now()
  for i in range(len(t00)) : # loop over the time intervals
    #print "FITS data generation loop begins: ", datetime.now()
    c.execute('SELECT * FROM events WHERE PACKET_TIME BETWEEN ? and ? ORDER BY PACKET_TIME', (t00[i], t11[i])) #JKB 4/29/2019 added +/- 20 for offset correction, now using headers rather than event times
    d1 = c.fetchall() # fetch all the rows into the list d1
    for r in d1 : d.append(r) # append each row to d
  
    if (loud > 2) : print('Read ', len(d), ' rows from database.')
    #print 'DB query finished'
    #print "Query completed at: ", datetime.now()
    #!!! include lines to remove duplicate entries

    # each row in d consists of a tuple of numbers with the order setup by
    # the command used to define the data table which is
    # Truncated time, Pha, DPU ID, Packet Time (which is header time)
    # !!! it would be nice to do the extract using names for the columns
    # !!! figure out how to do this - seems that can be done only row by row

    #%% copy data into arrays
    # define and fill numpy arrays for the quantities in the data table
    invalid14=0
    invalid54=0
    invalid38=0
    for i in range(len(d)):
      dpu_id = d[i][2] # event DPU !!! weird order
      if dpu_id == 14:
        j=0
        try:
            tdo=offset14[d[i][3]]
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:
            time=-1
            invalid14+=1
      if dpu_id == 38:
        j=2
        try: 
            tdo=offset38[d[i][3]] 
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:	
            time=-1
            invalid38+=1
      if dpu_id == 54:
        j=1
        try:
            tdo=offset54[d[i][3]]
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:
            time=-1
            invalid54+=1
      for x in range(len(t0)):
        if time >= t0[x] and time <= t1[x]:      
          # event pulse height
          pha =  d[i][1]
          pi = (c1[j]*pha+c2[j])/(1000*ebin)
          dputxt.write(str(dpu_id)+'\n')
          phatxt.write(str(pha)+'\n')
          timtxt.write(str(time)+'\n')
          pitxt.write(str(pi)+'\n')
    if invalid14 > 0:
        print('DPU 14 missing time offset for',d[i][3],'thousand seconds packet time.')
        print(invalid14,"orphaned DPU 14 events removed for packet time",d[i][3],".")
    if invalid38 > 0:
        print('DPU 38 missing time offset for',d[i][3],'thousand seconds packet time.')
        print(invalid38,"orphaned DPU 38 events removed for packet time",d[i][3],".")
    if invalid54 > 0:
        print('DPU 54 missing time offset for',d[i][3],'thousand seconds packet time.')
        print(invalid54,"orphaned DPU 54 events removed for packet time",d[i][3],".")
    d = [] #clear mem
  db.close() # close the connection to the database
  dputxt.close() 
  phatxt.close()
  timtxt.close()
  pitxt.close()
  dputxt = open(tempdpu,"r") 
  tai_time=[]
  pha=[]
  pi=[]
  dpu_id=[]
  for line in dputxt:
      dpu_id.append(int(line))
  dputxt.close()
  c_dpuid = pyfits.Column(name='DPU_ID', format='I', unit='', array=dpu_id)
  dpu_id=0
  phatxt = open(temppha,"r")
  for line in phatxt:
      pha.append(int(line))
  phatxt.close()
  c_pha = pyfits.Column(name='PHA', format='I', unit='', array=pha)
  pha=0
  pitxt = open(temppi,"r")
  for line in pitxt:
      pi.append(float(line))
  pitxt.close()
  c_pi = pyfits.Column(name='PI', format='D', unit=pi_unit, array=pi)
  pi=0
  timtxt = open(temptime,"r")
  for line in timtxt:
      tai_time.append(float(line))
  timtxt.close()
  c_time = pyfits.Column(name='TIME', format='D', unit='s', array=tai_time) #tai time is used later, so we do not clear this one from mem.

  #delete temp TXTs
  os.remove(temptime)
  os.remove(tempdpu)
  os.remove(temppha)
  os.remove(temppi)

  #%% write the data in arrays out to a FITS file
  # write event data to a FITS file with name fits_name
  prihdr = pyfits.Header() # create header for FITS file
  prihdr['MISSION'] = 'HaloSat'
  # date and time of file creation
  prihdr['SYSTIME'] = (str(datetime.now()), 'FITS file creation time')
  prihdr['MINTIME'] = (min(tai_time), 'Earliest time for spacecraft data')
  prihdr['MAXTIME'] = (max(tai_time), 'Latest time for spacecraft data')
  prihdr['MIN_GTI'] = (gtimin, 'Minimal good time interval allowed')
  prihdr['MAX_OFF'] = (DELTA, 'Allowed pointing degree offset')
  # create primary HDU
  prihdu = pyfits.PrimaryHDU(header=prihdr)
  # create columns for FITS file
  # combine columns
  cols = pyfits.ColDefs([c_time, c_dpuid, c_pha, c_pi])
  # create binary table HDU
  tbhdu = pyfits.BinTableHDU.from_columns(cols)
  # add comments, note this depends on the order the columns are written
  tbhdu.header.comments['TTYPE1'] = 'Event time in TAI seconds since 2000-01-01'
  tbhdu.header.comments['TTYPE2'] = 'Data processing unit that recorded event'
  tbhdu.header.comments['TTYPE3'] = 'Event pulse height'
  tbhdu.header.comments['TTYPE4'] = 'Event pulse invariant'

  # write header and table to FITS file
  thdulist = pyfits.HDUList([prihdu, tbhdu])
  #print "FITS generated, writing FITS starts now: ", datetime.now()
  thdulist.writeto(fits_name, overwrite=True)
  thdulist.close()

  if (loud > 2) :
    print('Wrote ', str(n), ' rows of data to ', fits_name)
    print('Covering times from ', min(tai_time), ' to ', max(tai_time))

def evt2fits(dbname, fits_name, t0, t1, gtimin, DELTA, pha_cut=[], loud=0) :
  """
  Read from an SQLite database for instrument event data for HaloSat
  and write the data to a FITS file.
  dbname is name of database file, can include a full or relative path.
  fits_name is name of output FITS file, can include a full or relative path.
  t0 is a list/array of start times of intervals.
  t1 is a list/array of end times of intervals.
  Times are in TAI seconds since 2000-01-01T00:00:00 UTC per BCT's useage.
  pha_cut is a list of lower and upper bounds on the PHA values for events
  written to the FITS file.  If empty, all events are written.  If one pair
  of numbers, then the same cuts are applied to all DPUs.  If three pairs
  of numbers, then each DPU gets its own cuts.
  loud : 0 for no printing, >= 1 for differing levels of printing
  """

  # information for conversion from PHA to PI
  # taken from Anna's !!!
  # !!! should really look this up in a database in case the conversion changes with time
  #print 'Starting event writing...'
  #dpu_list = [14, 54, 38] #unused
  c1 = [0.5440, 0.5496, 0.5770] # coefficients for conversion of ADC channels to eV
  c2 = [-30.5, -36.3, -34.6]    # E = C1*PHA + C2
  ebin = 0.01 # [keV] energy bin size for PI
  pi_unit = str(1000*ebin)+ 'eV'

  # read the data table from the database
  db = sqlite3.connect(dbname) # open database to store spacecraft data
  c = db.cursor() # make a cursor into database
  
  # execute SQL commands to select all rows in the specified time intervals
  # in the spacecraft data table
  offset14={}#Generate timeoffset dictionaries
  offset38={}
  offset54={}
  t00=[]
  t11=[]
  rfr=type('stuff')
  pha2='stuff'
  #%
  for i in range(len(t0)) : # loop over the time intervals, truncate to match DB stored values, and merge if intervals would overlap in widened DB search
    val=str(t0[i])
    val=val[0:6]
    val=int(val)
    val2=str(t1[i])
    val2=val2[0:6]
    val2=int(val2)+1
    if len(t00)>0 and val<=t11[len(t11)-1]:
      t11[len(t11)-1]=val2
    else:
      t00.append(val) #at this point, we've converted (roughly) event times back into header times to use to search the DB
      t11.append(val2)
  for i in range(len(t00)):
    c.execute('SELECT * FROM offsets14 WHERE pkt_time_14 BETWEEN ? and ?', (t00[i], t11[i]))
    offs1=c.fetchall()
    for x in range(len(offs1)):
          offset14[offs1[x][1]]=offs1[x][0] #use header time as dict key to find offset, dict for each DPU
    c.execute('SELECT * FROM offsets38 WHERE pkt_time_38 BETWEEN ? and ?', (t00[i], t11[i]))
    offs2=c.fetchall()
    for x in range(len(offs2)):
          offset38[offs2[x][1]]=offs2[x][0]
    c.execute('SELECT * FROM offsets54 WHERE pkt_time_54 BETWEEN ? and ?', (t00[i], t11[i]))
    offs3=c.fetchall()
    for x in range(len(offs3)):
          offset54[offs3[x][1]]=offs3[x][0]
  offs1=0 #clear as much mem as possible
  offs2=0
  offs3=0
  d = [] # where the data will go
  #print 'fetching data from DB'
  for i in range(len(t00)) : # loop over the time intervals
    tai_time=0
    pha=0
    dpu_id=0
    pi=0
    c.execute('SELECT * FROM events WHERE PACKET_TIME BETWEEN ? and ? ORDER BY PACKET_TIME', (t00[i], t11[i])) #JKB 4/29/2019 added +/- 20 for offset correction, now using headers rather than event times
    d1 = c.fetchall() # fetch all the rows into the list d1
    for r in d1 : d.append(r) # append each row to d
  
    if (loud > 2) : print('Read ', len(d), ' rows from database.')
    #!!! include lines to remove duplicate entries

    # each row in d consists of a tuple of numbers with the order setup by
    # the command used to define the data table which is
    # Truncated time, Pha, DPU ID, Packet Time (which is header time)
    # !!! it would be nice to do the extract using names for the columns
    # !!! figure out how to do this - seems that can be done only row by row

    #%% copy data into arrays
    # define and fill numpy arrays for the quantities in the data table
    d2=[] #filter list d for valid times after doing offsets.
    invalid14=0
    invalid38=0
    invalid54=0
    for i in range(len(d)):
      dpu_id = d[i][2] # event DPU !!! weird order
      if dpu_id == 14:
        j=0
        try:
            tdo=offset14[d[i][3]]
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:
            time=-1
            invalid14+=1
      if dpu_id == 38:
        j=2
        try: 
            tdo=offset38[d[i][3]] 
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:	
            time=-1
            invalid38+=1
      if dpu_id == 54:
        j=1
        try:
            tdo=offset54[d[i][3]]
            time = d[i][0] + tdo # event time, takes trunc time and adds matching offset using packet time
        except:
            time=-1
            invalid54+=1
      for x in range(len(t0)):
        if time >= t0[x] and time <= t1[x]:      
          # event pulse height
          pha =  d[i][1]
          pi = (c1[j]*pha+c2[j])/(1000*ebin)
          z = [time, pha, dpu_id, pi]
          d2.append(z)  #after this, code merges back to what it used to be
    if invalid14 > 0:
    	print("Events removed due to invalid or unmatched packet times for DPU 14: ",invalid14,", at time: ",d[i][3], ' thousand seconds.')
    if invalid38 > 0:
    	print("Events removed due to invalid or unmatched packet times for DPU 38: ",invalid38,", at time: ",d[i][3], ' thousand seconds.')
    if invalid54 > 0:
    	print("Events removed due to invalid or unmatched packet times for DPU 54: ",invalid54,", at time: ",d[i][3], ' thousand seconds.')
    n = len(d2) # the length of d is the number of rows of data
    d = [] #clear mem
    # define the numpy arrays
    #print 'data len', n
    tai_time, dpu_id = zeros(n), zeros(n, int) # time and DPU_ID
    # event pulse height
    pha = zeros(n, int)
    # pulse height invariant, converted to eV
    pi = zeros(n)
    # loop over d and write the values into the appropriate arrays
    for i in range(n) :
      tai_time[i] = d2[i][0]
      dpu_id[i] = d2[i][2] # event DPU !!! weird order
      # event pulse height
      pha [i] =  d2[i][1]
      pi[i] = d2[i][3]
    #print 'arrays finished'
    #  apply PHA cuts to events
    # !!! need to write
    d2=[] #clear mem
    p2t=type(pha2)
    if p2t == rfr:
      pha2=pha
      tai_time2=tai_time
      dpu_id2=dpu_id
      pi2=pi
    else:
      pha2=np.concatenate((pha2,pha),axis=0)
      pi2=np.concatenate((pi2,pi),axis=0) #move pulse invariant later, append as new column???
      tai_time2=np.concatenate((tai_time2,tai_time),axis=0)
      dpu_id2=np.concatenate((dpu_id2,dpu_id),axis=0)

  #%% write the data in arrays out to a FITS file
  # write event data to a FITS file with name fits_name
  db.close() # close the connection to the database
  prihdr = pyfits.Header() # create header for FITS file
  prihdr['MISSION'] = 'HaloSat'
  # date and time of file creation
  prihdr['SYSTIME'] = (str(datetime.now()), 'FITS file creation time')
  prihdr['MINTIME'] = (min(tai_time2), 'Earliest time for spacecraft data')
  prihdr['MAXTIME'] = (max(tai_time2), 'Latest time for spacecraft data')
  prihdr['MIN_GTI'] = (gtimin, 'Minimal good time interval allowed')
  prihdr['MAX_OFF'] = (DELTA, 'Allowed pointing degree offset')
  # create primary HDU
  prihdu = pyfits.PrimaryHDU(header=prihdr)
  # create columns for FITS file
  c_time = pyfits.Column(name='TIME', format='D', unit='s', array=tai_time2)
  c_dpuid = pyfits.Column(name='DPU_ID', format='I', unit='', array=dpu_id2)
  c_pha = pyfits.Column(name='PHA', format='I', unit='', array=pha2)
  c_pi = pyfits.Column(name='PI', format='D', unit=pi_unit, array=pi2)
  # combine columns
  cols = pyfits.ColDefs([c_time, c_dpuid, c_pha, c_pi])
  # create binary table HDU
  tbhdu = pyfits.BinTableHDU.from_columns(cols)
  # add comments, note this depends on the order the columns are written
  tbhdu.header.comments['TTYPE1'] = 'Event time in TAI seconds since 2000-01-01'
  tbhdu.header.comments['TTYPE2'] = 'Data processing unit that recorded event'
  tbhdu.header.comments['TTYPE3'] = 'Event pulse height'
  tbhdu.header.comments['TTYPE4'] = 'Event pulse invariant'

  # write header and table to FITS file
  thdulist = pyfits.HDUList([prihdu, tbhdu])
  thdulist.writeto(fits_name, overwrite=True)
  thdulist.close()

  if (loud > 2) :
    print('Wrote ', str(n), ' rows of data to ', fits_name)
    print('Covering times from ', min(tai_time2), ' to ', max(tai_time2))

def ecef2eci(ecef,tai_time):
  """
  Shamelessly stolen from pyorbital.astronomy.py
  Convert ECEF (Earth Centered Earth Fixed) positions to ECI (Earth Centered Inertial)
  http://ccar.colorado.edu/ASEN5070/handouts/coordsys.doc
   [X] [C -S 0][X]
   [Y] = [S C 0][Y]
   [Z]eci [0 0 1][Z]ecf
   C and S are cos() and sin() of gmst (Greenwich Meridian Sideral Time)
  Inspired from satellite-js (https://github.com/shashwatak/satellite-js)
  """
  def gmst(tai_time):
    # ut1 is the centuries since J2000 (which is at 2000-01-01T12:00:00 or TAI time 43236)
    tai_days = (tai_time-43236)/(3600.*24)
    tai_centuries = tai_days/(365.25*100)
    theta = 67310.54841 + \
            tai_centuries * (876600 * 3600 + 8640184.812866) + \
            tai_centuries**2 * (0.093104) - \
            tai_centuries**3 * (6.2e-6)
    return (pi/180*theta/240.0) % (2*pi)
  gmst2 = gmst(tai_time)
  eci = ecef.copy()
  eci[:,0] = ecef[:,0]*cos(gmst2) - ecef[:,1]*sin(gmst2)
  eci[:,1] = ecef[:,0]*sin(gmst2) + ecef[:,1]*cos(gmst2)
  eci=eci.T
  return eci

def haversine(ra, dec, ra2, dec2):
  """
  Computes the great circle distance between a set of
  coordinates (<ra>, <dec>) and a reference coordinate
  (<ra2>, <dec2>).
  Returns haversine angle distance {float}
  """
  ra   = ra*(pi/180)
  dec  = dec*(pi/180)
  ra2  = ra2*(pi/180)
  dec2 = dec2*(pi/180)

  dDEC = 0.5 * (dec - dec2)
  dRA = 0.5 * (ra - ra2)

  a = sin(dDEC)**2 + cos(dec)*cos(dec2)*sin(dRA)**2
  c = 2*arcsin(sqrt(a))*180/pi

  return(c)

if __name__ == '__main__':
  path1='/home/halosat/data/haloSat_targets.fits' #file path to haloSat_targets.fits
  dbpath1='/home/halosat/data/housekeeping.db'#'/disk2/housekeeping.db' #path to housekeeping database
  dbpath2='/home/halosat/data/science.db'#'/disk2/science.db' #path to science database
  flag = 0
  flag2 = 0
  delta = 0
  time_start=0
  time_end=10E15  
  timmy=datetime.now() #three lines to generate timestamp for file name
  timothy=str(timmy)
  timtim=timothy[0:4]+timothy[5:7]+timothy[8:10]
  try:
    N=sys.argv[1]
    N=int(N)
    gtimin=sys.argv[2]
    delta=sys.argv[3]
    gtimin=int(gtimin)
    delta=float(delta)
    if len(sys.argv)>4: #provided timecuts
        time_start,time_end=sys.argv[4],sys.argv[5]
        if len(sys.argv)>6: #secondary outfile name - would be better as argument 5 rather than 7, but preserving RR order. Used for checking sequential command line calls with external code. include .txt
            log_name=sys.argv[6]
            flag2 = 1	
    n="%04d" % (N,) #adds leading zeros for filename, if nec
    file_name='HS'+str(n)+'_'+timtim+'_raw.txt' #filename in HSnnnn_yyyymmdd_uf format
    stdoutOrigin=sys.stdout
    sys.stdout=open(file_name,"w")
    flag = 1
  except:
    N=input("What is your target ID number? (Do not include leading zeros):") #set target ID here.
    N=int(N)
    gtimin=input("Select a minimum good time interval size in seconds (recommended: 64 s):") #set gtimin here.
    gtimin=int(gtimin)
  run_str = ' with gti_min='+str(gtimin)+', offset<='+str(delta)+', start_time='+str(time_start)+', and end_time='+str(time_end)+'.'
  if N == 0 and flag == 0 and flag2 == 0:
    altsearch(gtimin,path1,dbpath1,dbpath2,timtim)
  elif flag2 == 0:
    proc_ID(N,gtimin,path1,dbpath1,dbpath2,flag,delta,time_start,time_end,timtim)
  if flag2 == 1:
    try:
        proc_ID(N,gtimin,path1,dbpath1,dbpath2,flag,delta,time_start,time_end,timtim)
        print('Searchdb run successful for '+str(N)+run_str)
        with open(log_name,'a') as lf: lf.write('\n\nSearchdb run successful for '+str(N)+run_str)
    except:
        print('Searchdb run failed for '+str(N)+run_str)
        with open(log_name,'a') as log_file: log_file.write('\n\nSearchdb run failed for '+str(N)+run_str)   
        sys.stdout.close()
        sys.stdout=stdoutOrigin  
    		 		
  if flag == 0:
    print("Process completed.")
