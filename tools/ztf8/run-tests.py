#!/usr/bin/python3

import sys, subprocess, os, optparse, re, codecs, stat, signal
import random
import time
from datetime import datetime
from time import monotonic as timer

# sudo sysctl -w kernel.perf_event_paranoid=0

outputFile = None
dataFolder = "/home/cameron/Wikibooks/"
#"~/Testfiles/"
MAX_ROUNDS = 1
SKIPPED_ROUNDS = 0
GATHER_CYCLE_COUNTS = False
COLOURS = [r"always", r"never"]
THREAD_COUNTS = [1] #[1,2,3,4]
EDIT_DISTANCES = [1,2,4,8] 
LENGTH = [1]
SEGMENT_SIZES = []#[1] + [x for x in range(4, 260, 4)]
ICGREP_RE_LIST = [r"\p{Greek}", r"\X"] 
TIMEOUT=300

def getCurrentUser():
    proc = subprocess.run("whoami", stdout=subprocess.PIPE, shell=True)
    user = codecs.decode(proc.stdout, 'utf-8')
    return user
    

currentUser = getCurrentUser()

def anyOtherUsersAreOn():
    proc = subprocess.run("who | grep -vc '^$%s'" % (currentUser), stdout=subprocess.PIPE, shell=True)
    out = codecs.decode(proc.stdout, 'utf-8')
    r = int(out) != 0
    return r
        
def extractKernelProfile(out):
    if GATHER_CYCLE_COUNTS:
        data = re.findall("^\s*[0-9]+(?:\s+\S+){10}\s+([0-9.]+)", out, re.MULTILINE)
        largest = 0.0
        for i in range(len(data)):
            largest = max(largest, float(data[i]))
        return str(len(data)) + "," + str(largest)
    else:
        return out

def exec_test(appcode, cmd, config, keepresult, outputFileName):
    try:        
        print(cmd, "at", datetime.now().strftime("%d/%m/%Y %H:%M:%S"))
        #start = timer()
        with subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, shell=True, preexec_fn=os.setsid) as process:
            try:
                #result = process.communicate(timeout=TIMEOUT)[1]
                result = process.communicate()[1]
            except:
                print(" --- timed out at", datetime.now().strftime("%d/%m/%Y %H:%M:%S"))
                os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                return 1
        #proc = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, shell=True, timeout=2)
        anyOtherUsers = anyOtherUsersAreOn()
        # open(os.path.dirname(outputFileName) + "/run-tests-running", "w")

        outputFile = open(outputFileName, "w")
    
        # os.remove(os.path.dirname(outputFileName) + "/run-tests-running")
        outputFile.write(u"%s\n" % (extractKernelProfile(codecs.decode(result, 'utf-8'))))
        if anyOtherUsers or not keepresult:
            outputFile.write(u"")
        outputFile.flush()
        outputFile.close()
        return not anyOtherUsers
    except subprocess.CalledProcessError as e:
        print(codecs.decode(e.output, 'utf-8'))
        return False
    
def exec_tests(appcode, cmd, config, outputFile):
    cmd = cmd.encode('utf-8')
    toignore = SKIPPED_ROUNDS
    rounds = 0
    while True:
        if exec_test(appcode, cmd, config, toignore == 0, outputFile):
            if toignore == 0:
                rounds += 1
                if rounds >= MAX_ROUNDS:
                    break
            else:
                toignore -= 1
        else:
            print("...interupted")
            while True:
                time.sleep(60)
                if not anyOtherUsersAreOn():
                    break
            time.sleep(15)
            toignore = SKIPPED_ROUNDS
    # outputFile.flush()

def run_parabix_test(appcode, application, threadnum, length, segmentsize, segmentsizecoeff, args, config, outputFile):
    cmd = r"%s --thread-num=%d --length=%d %s" % (application, threadnum, length, args)
    exec_tests(appcode, cmd, str(threadnum) + "," + config, outputFile)

def run_threaded_tests(appcode, application, segmentsizecoeff, args, config, outputFile):
    print(appcode, "appcode")
    print(application, "application")
    # print(threadnum, "threadnum")
    print(segmentsizecoeff, "segmentsizecoeff")
    print(args, "args")
    print(config, "config")
    for threadnum in THREAD_COUNTS:
        for length in LENGTH:
            run_parabix_test(appcode, application, threadnum, length, 16384, segmentsizecoeff, args, config, outputFile)

def run_data_test(appcode, application, segmentsizecoeff, args, dataFile, config, outputFile):
    run_threaded_tests(appcode, application, segmentsizecoeff, args + " " + dataFolder + dataFile, config, outputFile)
    
def run_all_data_test(appcode, application, segmentsizecoeff, args, suffix, config):
    # print(suffix, "suffix")
    # print(config, "config")
    # run_data_test(appcode, application, segmentsizecoeff, args, "enwik8", config + "enwik8", "enwik8.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "arwikibooks-20150102-pages-articles.xml", config + "arwiki", "arwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "dewikibooks-20141216-pages-articles.xml", config + "dewiki", "dewiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "elwikibooks-20141226-pages-articles.xml", config + "elwiki", "elwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "eswikibooks-20141223-pages-articles.xml", config + "eswiki", "eswiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "fawikibooks-20141217-pages-articles.xml", config + "fawiki", "fawiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "fiwikibooks-20141221-pages-articles.xml", config + "fiwiki", "fiwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "frwikibooks-20150106-pages-articles.xml", config + "frwiki", "frwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "idwikibooks-20141221-pages-articles.xml", config + "idwiki", "idwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "jawikibooks-20150103-pages-articles.xml", config + "jawiki", "jawiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "kowikibooks-20141223-pages-articles.xml", config + "kowiki", "kowiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "ruwikibooks-20150123-pages-articles.xml", config + "ruwiki", "ruwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "thwikibooks-20150104-pages-articles.xml", config + "thwiki", "thwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "trwikibooks-20141227-pages-articles.xml", config + "trwiki", "trwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "viwikibooks-20141221-pages-articles.xml", config + "viwiki", "viwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "zhwikibooks-20141225-pages-articles.xml", config + "zhwiki", "zhwiki.csv")
    run_data_test(appcode, application, segmentsizecoeff, args, "wiki-books-all.xml", config + "wikiall", "wikiall.csv")
    # -20210501-pages-articles-multistream-index.txt" + suffix, config + "Enwiki")
    # run_data_test(appcode, application, segmentsizecoeff, args, "zhwiki-20210501-pages-articles-multistream1.xml-p1p187712" + suffix, config + "Zhwiki")
    # run_data_test(appcode, application, segmentsizecoeff, args, "ruwiki-20211101-pages-articles-multistream1.xml-p1p224167" + suffix, config + "Ruwiki")
    # run_data_test(appcode, application, segmentsizecoeff, args, "arwiki-20211101-pages-articles-multistream3.xml-p1205739p2482315" + suffix, config + "Arwiki")
    
    
    
def run_data_tests(appcode, application, segmentsizecoeff, args, config):
    run_all_data_test(appcode, application, segmentsizecoeff, args, "", config)

def run_u32_tests(appcode, application, segmentsizecoeff, args, config):
    run_all_data_test(appcode, application, segmentsizecoeff, args, ".u32", config)


def run_gb_tests(appcode, application, segmentsizecoeff, args, config):
    run_all_data_test(appcode, application, segmentsizecoeff, args, ".gb18030", config)

def run_decomp_tests(appcode, application, segmentsizecoeff, args, config):
    run_all_data_test(appcode, application, segmentsizecoeff, args, ".ztf", config)

def run_csv_tests(appcode, application, segmentsizecoeff, args, config):
    run_data_test(appcode, application, segmentsizecoeff, args, "annual-enterprise-survey-2020-financial-year-provisional-csv.csv", config + "Fin")
    run_data_test(appcode, application, segmentsizecoeff, args, "output_csv_full.csv", config + "Trade")
    run_data_test(appcode, application, segmentsizecoeff, args, "Data8277.csv", config + "Census")

def run_ugrep_test(appcode, cmd, config):
    exec_tests(appcode, cmd + "enwiki-20210501-pages-articles-multistream-index.txt", config + "Enwiki")
    exec_tests(appcode, cmd + "zhwiki-20210501-pages-articles-multistream1.xml-p1p187712", config + "Zhwiki")
    exec_tests(appcode, cmd + "ruwiki-20211101-pages-articles-multistream1.xml-p1p224167", config + "Ruwiki")
    exec_tests(appcode, cmd + "arwiki-20211101-pages-articles-multistream3.xml-p1205739p2482315", config + "Arwiki")
    
def run_ugrep_tests(appcode, application):
    for expr in [r"\p{Greek}", r"\X"]: 
        for colors in COLOURS:   
            cmd = application + " '" + expr + "' -a --colours=" + colors + " " + dataFolder
            config = "1,1," + expr + "," + colors + ","
            run_ugrep_test(appcode, cmd, config)

def run_ugrep_expr_tests(appcode, application):
    names = [r"@", r"Date", r"Email", r"URIOrEmail", r"Xquote"]
    exprs = [r"@", 
             r"([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)", 
             r"([^ @]+)@([^ @]+)", 
             r"([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)", 
             "[\"’]|&quot;|&apos;|&#0*3[49];|&#x0*2[27];"]
    for name, expr in zip(names, exprs):
        for colors in COLOURS:
            cmd = application + " '" + expr + "' -a --colours=" + colors + " " + dataFolder
            config = "1,1," + name + "," + colors + ","
            run_ugrep_test(appcode, cmd, config)



def run_2017_expr_tests(appcode, application, segmentsizecoeff, args, config):
    names = [r"@", r"Date", r"Email", r"URIOrEmail", r"Xquote"]
    exprs = [r"@", r"([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)", r"([^ @]+)@([^ @]+)", r"([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)", "[\"’]|&quot;|&apos;|&#0*3[49];|&#x0*2[27];"]
    for name, expr in zip(names, exprs):
            added_args = args + " '" + expr + "'"
            run_all_data_test(appcode, application, segmentsizecoeff, added_args, "", name + ",never," + config)

def run_expr_tests(appcode, application, segmentsizecoeff, args, config):
    names = [r"@", r"Date", r"Email", r"URIOrEmail", r"Xquote"]
    exprs = [r"@", 
    r"([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)", 
    r"([^ @]+)@([^ @]+)", 
    r"([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)", 
    r"[\"’]|&quot;|&apos;|&#0*3[49];|&#x0*2[27];"]
    for name, expr in zip(names, exprs):
        for colors in COLOURS:  
            added_args = args + " '" + expr + "' -colors=" + colors
            run_all_data_test(appcode, application, segmentsizecoeff, added_args, "", name + "," + colors + "," + config)

def run_jump_tests(appcode, application, segmentsizecoeff, args, config):
    for expr in ICGREP_RE_LIST:
        for colors in COLOURS: 
            added_args = args + " '" + expr + "' -colors=" + colors
            run_all_data_test(appcode, application, segmentsizecoeff, added_args, "", expr + "," + colors + "," + config)


def run_editd_tests(appcode, application, segmentsizecoeff, args, config):
    args = args + r" -enable-multieditd-kernels --prefix=100 -f %s/100reads %s/chr1.fa" % (dataFolder, dataFolder)
    for editdist in EDIT_DISTANCES:
        added_args = args + " -edit-dist=%d" % (editdist)
        run_threaded_tests(appcode, application, segmentsizecoeff, added_args, str(editdist))
    
def run_base64_tests(appcode, application):  
    exec_tests(appcode, application % ("enwiki-20210501-pages-articles-multistream-index.txt"), "1,1,Enwiki")
    exec_tests(appcode, application % ("zhwiki-20210501-pages-articles-multistream1.xml-p1p187712"), "1,1,Zhwiki")  
    exec_tests(appcode, application % ("ruwiki-20211101-pages-articles-multistream1.xml-p1p224167"), "1,1,Ruwiki") 
    exec_tests(appcode, application % ("arwiki-20211101-pages-articles-multistream3.xml-p1205739p2482315"), "1,1,Arwiki") 
        
def run_csv2json_tests(appcode, application):  
    exec_tests(appcode, application % ("annual-enterprise-survey-2020-financial-year-provisional-csv.csv"), "1,1,Fin")
    exec_tests(appcode, application % ("output_csv_full.csv"), "1,1,Trade")
    exec_tests(appcode, application % ("Data8277.csv"), "1,1,Census")    
        
        
def run_ugrep_tests2(appcode, application, args):  
    args = args + "-a -f ~/data/spamassassin-set"
    for expr in ["1", "2", "3", "Y", "5", "6"]:
        run_data_test(appcode, application, 4096, args + expr, "enron.merged", "f" + expr + ",Enron")
        run_data_test(appcode, application, 4096, args + expr, "enwiki-20210501-pages-articles-multistream-index.txt", "f" + expr + ",Enwiki")
        run_data_test(appcode, application, 4096, args + expr, "zhwiki-20210501-pages-articles-multistream1.xml-p1p187712", "f" + expr  + ",Zhwiki")
            
def run_utf8lut_tests(appcode, application, config):    
    exec_tests(appcode, application % ("enwiki-20210501-pages-articles-multistream-index.txt"), "Enwiki," + config)
    exec_tests(appcode, application % ("zhwiki-20210501-pages-articles-multistream1.xml-p1p187712"), "Zhwiki," + config)    
    exec_tests(appcode, application % ("ruwiki-20211101-pages-articles-multistream1.xml-p1p224167"), "Ruwiki," + config) 
    exec_tests(appcode, application % ("arwiki-20211101-pages-articles-multistream3.xml-p1205739p2482315"), "Arwiki," + config) 
        
        
optLevelConfig="-optimization-level=standard -backend-optimization-level=standard"    

def extract_data_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_data_tests(appcode, application, 4096, args, config)

def extract_decomp_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_decomp_tests(appcode, application, 4096, args, config)

def extract_gb_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_gb_tests(appcode, application, 4096, args, config)

def extract_csv_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_csv_tests(appcode, application, 4096, args, config)

def extract_edit_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_editd_tests(appcode, application, 4096, args, config)

def extract_u32_profile_costs(appcode, application, args, config):    
    args += " -EnableCycleCounter"
    run_u32_tests(appcode, application, 4096, args, config)

def extract_icgrep_cycle_profile_costs(appcode, application, args, config):  
    args += " -EnableCycleCounter"
    run_expr_tests(appcode, application, 4096, args, config)
    run_jump_tests(appcode, application, 4096, args, config)
    
if __name__ == '__main__':
    if len(sys.argv) != 1:
        print('python %prog <output filename>')
        sys.exit(1)
    print("starting at", datetime.now().strftime("%d/%m/%Y %H:%M:%S"))
    
    # outputFileName = os.path.abspath(sys.argv[1])

    # open(os.path.dirname(outputFileName) + "/run-tests-running", "w")


    # outputFile = open(outputFileName, "w")

    # time.sleep(10)

    ##run_editd_tests("EL", "~/workspace/parabix-linda/build/editd", 16, "", "") # internally scales by blockwidth (256)
    #run_editd_tests("ET", "~/workspace/parabix-devel/build/bin/editd", 4096, optLevelConfig, "")
    ##run_editd_tests("EX2020", "~/workspace/parabix-devel/build-2020/bin/editd", 4096, optLevelConfig, "")

    ##run_data_tests("BLR2", "~/workspace/parabix-linda/build/base64", 16 * 3, "", "") # internally scales by blockwidth (256)
    run_data_tests("ZTF", "~/parabix-devel/build12/bin/ztf-phrase-hash", 4096, optLevelConfig, "")
    ##run_data_tests("BT2020", "~/workspace/parabix-devel/build-2020/bin/base64", 4096, optLevelConfig, "")

    ##run_data_tests("UL", "~/workspace/parabix-linda/build/u8u16", 16, "", "") # internally scales by blockwidth (256)
    #run_data_tests("UO", "~/workspace/parabix-devel/build-u8u16/bin/u8u16", 4096, optLevelConfig, "")
    #run_data_tests("UT2", "~/workspace/parabix-devel/build/bin/u8u16", 4096, optLevelConfig, "")
    ##run_data_tests("UX2020", "~/workspace/parabix-devel/build-2020/bin/u8u16", 4096, optLevelConfig, "")

    #run_u32_tests("U32T2", "~/workspace/parabix-devel/build/bin/u32u8", 4096, optLevelConfig, "")
    ##run_u32_tests("U322020", "~/workspace/parabix-devel/build-2020/bin/u32u8", 4096, optLevelConfig, "")

    ##run_gb_tests("GO", "~/workspace/parabix-devel/build-2020/bin/gb18030", 4096, optLevelConfig, "")
    #run_gb_tests("GT", "~/workspace/parabix-devel/build/bin/gb18030", 4096, optLevelConfig, "")

    ##run_data_tests("ZCO", "~/workspace/parabix-devel/build-2020/bin/ztf-hash", 4096, optLevelConfig, "")
    #run_data_tests("ZCT", "~/workspace/parabix-devel/build/bin/ztf-hash", 4096, optLevelConfig, "")

    ##run_decomp_tests("ZDO", "~/workspace/parabix-devel/build-2020/bin/ztf-hash", 4096, "-d " + optLevelConfig, "")
    #run_decomp_tests("ZDT", "~/workspace/parabix-devel/build/bin/ztf-hash", 4096, "-d " + optLevelConfig, "")

    ##run_csv_tests("CJO", "~/workspace/parabix-devel/build-2020/bin/csv2json", 4096, optLevelConfig, "")
    #run_csv_tests("CJT", "~/workspace/parabix-devel/build/bin/csv2json", 4096, optLevelConfig, "")  

    ##run_jump_tests("IJO", "~/workspace/parabix-devel/build-2020/bin/icgrep", 4096, optLevelConfig, "") 
    ##run_expr_tests("IJO", "~/workspace/parabix-devel/build-2020/bin/icgrep", 4096, optLevelConfig, "") 
    
    #run_jump_tests("IJT", "~/workspace/parabix-devel/build/bin/icgrep", 4096, optLevelConfig, "")
    #run_expr_tests("IJT", "~/workspace/parabix-devel/build/bin/icgrep", 4096, optLevelConfig, "")

#    run_2017_expr_tests("IJL", "~/workspace/parabix-linda/build/icgrep", 16, "", "") 

#    run_ugrep_tests2("IFO", "~/workspace/parabix-devel/build-2020/bin/icgrep", optLevelConfig)
#    run_ugrep_tests2("IFT", "~/workspace/parabix-devel/build/bin/icgrep", optLevelConfig)

#    run_base64_tests("BXE", "~/workspace/base64/bin/base64 ~/data/%s")
#    run_csv2json_tests("CXE", "~/workspace/webcarrot-csv2json/csv2json -i ~/data/%s -o /dev/null")
#    run_utf8lut_tests("U8XE", "~/workspace/utf8lut/build/FileConverter -s=utf-8 -d=utf-16 -ec ~/data/%s /dev/null", "1,1")
#    run_utf8lut_tests("U32XE", "~/workspace/utf8lut/build/FileConverter -s=utf-32 -d=utf-8 -ec ~/data/%s.u32 /dev/null", "1,8")
#    run_ugrep_expr_tests("IJU", "~/workspace/ugrep/bin/ugrep")
#    run_ugrep_tests("IJU", "~/workspace/ugrep/bin/ugrep")
 
#    run_data_tests("BTH", "~/workspace/parabix-devel/build/bin/base64", 4096, optLevelConfig + " --enable-hybrid-thread-model=1", "")
#    run_jump_tests("IJTH", "~/workspace/parabix-devel/build/bin/icgrep", 4096, optLevelConfig + " --enable-hybrid-thread-model=1", "")
#    run_expr_tests("IJTH", "~/workspace/parabix-devel/build/bin/icgrep", 4096, optLevelConfig + " --enable-hybrid-thread-model=1", "")
#    run_data_tests("UTH", "~/workspace/parabix-devel/build/bin/u8u16", 4096, optLevelConfig + " --enable-hybrid-thread-model=1", "")
#    run_editd_tests("ETH", "~/workspace/parabix-devel/build/bin/editd", 4096, optLevelConfig + " --enable-hybrid-thread-model=1", "")    
    
    #PAPI_CL = optLevelConfig + " -PapiCounters=PAPI_TOT_CYC,PAPI_L2_TCM,PAPI_L3_TCM -DisplayPAPICounterThreadTotalsOnly"
    #PAPI_DT = PAPI_CL + " -DisableThreadLocalStreamSets"
    
    #for i in range(5):
        #run_data_tests("BTC", "~/workspace/parabix-devel/build/bin/base64", 4096, PAPI_CL, "")
        #run_data_tests("BTCD", "~/workspace/parabix-devel/build/bin/base64", 4096, PAPI_DT, "")
        #run_csv_tests("CJC", "~/workspace/parabix-devel/build/bin/csv2json", 4096, PAPI_CL, "")   
        #run_csv_tests("CJCD", "~/workspace/parabix-devel/build/bin/csv2json", 4096, PAPI_DT, "")   
        #run_gb_tests("GTC", "~/workspace/parabix-devel/build/bin/gb18030", 4096, PAPI_CL, "")
        #run_gb_tests("GTCD", "~/workspace/parabix-devel/build/bin/gb18030", 4096, PAPI_DT, "")
        #run_jump_tests("IJC", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_CL, "")    
        #run_jump_tests("IJCD", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_DT, "")    
        
#    PAPI_CL = optLevelConfig + " -PapiCounters=PAPI_TOT_CYC,PAPI_L2_TCM,PAPI_L3_TCM -DisplayPAPICounterThreadTotalsOnly"
#    PAPI_DT = PAPI_CL + " --enable-hybrid-thread-model=1"
    
#    run_data_tests("xBTC", "~/workspace/parabix-devel/build/bin/base64", 4096, PAPI_CL, "")
#    run_data_tests("xBTCH", "~/workspace/parabix-devel/build/bin/base64", 4096, PAPI_DT, "")
#    run_jump_tests("xIJC", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_CL, "")    
#    run_jump_tests("xIJCH", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_DT, "") 
#    run_expr_tests("xIJC", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_CL, "")
#    run_expr_tests("xIJCH", "~/workspace/parabix-devel/build/bin/icgrep", 4096, PAPI_DT, "")
#    run_data_tests("xUT", "~/workspace/parabix-devel/build/bin/u8u16", 4096, PAPI_DT, "")    
#    run_data_tests("xUTH", "~/workspace/parabix-devel/build/bin/u8u16", 4096, PAPI_DT, "")
    
    GATHER_CYCLE_COUNTS = False

    #extract_data_profile_costs("base64", "~/workspace/parabix-devel/build/bin/base64", optLevelConfig, "")
    #extract_csv_profile_costs("csv2json", "~/workspace/parabix-devel/build/bin/csv2json", optLevelConfig, "")
    #extract_edit_profile_costs("editd", "~/workspace/parabix-devel/build/bin/editd", optLevelConfig, "")
    #extract_gb_profile_costs("gb18030", "~/workspace/parabix-devel/build/bin/gb18030", optLevelConfig, "")	
    #extract_icgrep_cycle_profile_costs("icgrep", "~/workspace/parabix-devel/build/bin/icgrep", optLevelConfig, "")
    #extract_data_profile_costs("u8u16v2", "~/workspace/parabix-devel/build/bin/u8u16", optLevelConfig, "")
    #extract_data_profile_costs("ztfc", "~/workspace/parabix-devel/build/bin/ztf-hash", optLevelConfig, "")
    #extract_decomp_profile_costs("ztfd", "~/workspace/parabix-devel/build/bin/ztf-hash", optLevelConfig + " -d", "")    
    #extract_u32_profile_costs("u32u8v2", "~/workspace/parabix-devel/build/bin/u32u8", optLevelConfig, "")

    #extract_data_profile_costs("u8u16-old", "~/workspace/parabix-devel/build-u8u16/bin/u8u16", optLevelConfig, "")
    
    # outputFile.close()
    
    # os.remove(os.path.dirname(outputFileName) + "/run-tests-running")
    
    # print("finished at", datetime.now().strftime("%d/%m/%Y %H:%M:%S"), " : ", outputFileName)
