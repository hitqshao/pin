/*
 * Copyright (C) 2004-2021 Intel Corporation.
 * SPDX-License-Identifier: MIT
 */

/*! @file
 *  This file contains an ISA-portable cache simulator
 *  data cache hierarchies
 */

#include "pin.H"

#include <iostream>
#include <fstream>
#include <cassert>
#include <set>

#include "cache.H"
#include "pin_profile.H"
using std::cerr;
using std::endl;
using std::set;
using std::map;
using std::vector;

/* ===================================================================== */
/* Commandline Switches */
/* ===================================================================== */

KNOB< string > KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "dcache.out", "specify dcache file name");
KNOB< BOOL > KnobTrackLoads(KNOB_MODE_WRITEONCE, "pintool", "tl", "0", "track individual loads -- increases profiling time");
KNOB< BOOL > KnobTrackStores(KNOB_MODE_WRITEONCE, "pintool", "ts", "0", "track individual stores -- increases profiling time");
KNOB< UINT32 > KnobThresholdHit(KNOB_MODE_WRITEONCE, "pintool", "rh", "100", "only report memops with hit count above threshold");
KNOB< UINT32 > KnobThresholdMiss(KNOB_MODE_WRITEONCE, "pintool", "rm", "100",
                                 "only report memops with miss count above threshold");
KNOB< UINT32 > KnobCacheSize(KNOB_MODE_WRITEONCE, "pintool", "c", "32", "cache size in kilobytes");
KNOB< UINT32 > KnobLineSize(KNOB_MODE_WRITEONCE, "pintool", "b", "32", "cache block size in bytes");
KNOB< UINT32 > KnobAssociativity(KNOB_MODE_WRITEONCE, "pintool", "a", "4", "cache associativity (1 for direct mapped)");

/* ===================================================================== */
typedef struct FootPrintInfo {
    uint64_t currFoot;
    uint64_t increase;
    uint64_t recent100MFoot;
} FootPrintInfo;
/* ===================================================================== */

/* ===================================================================== */
static UINT64 instCnter = 0;

static void Count100MInst();

/*
    64 cacheblk will be merged into a 4KB page in pageRecord
    64 4KB page will be merged into 256KB hugepage in hugePageRecord
    16 256KB page will be merged into 4MB hugepage in superPageRecord
*/

//4M
static set<UINT64> superPageRecord;

//256KB
static set<UINT64> hugePageRecord;

//4KB
static set<UINT64> pageRecord;

static map<UINT64,set<ADDRINT> > memFootPrint4KB;

// footprint of recent 1B inst
static set<UINT64> memFootPrint1B;

// footprint of recent 100M inst
static set<UINT64> memFootPrint100M;

// memFootLen record
static UINT64 memFootLen = 0;

// Instead of write info into file every 100M, we write every 10B

static vector<FootPrintInfo> infoVec;

static std::ofstream file_out;

static const UINT64 CACHESIZE = 64;
/* ===================================================================== */

INT32 Usage()
{
    cerr << "This tool represents a cache simulator.\n"
            "\n";

    cerr << KNOB_BASE::StringKnobSummary();

    cerr << endl;

    return -1;
}

/* ===================================================================== */
/* Global Variables */
/* ===================================================================== */

// wrap configuation constants into their own name space to avoid name clashes
namespace DL1
{
const UINT32 max_sets                          = KILO*128; // cacheSize / (lineSize * associativity);
const UINT32 max_associativity                 = 256;  // associativity;
const CACHE_ALLOC::STORE_ALLOCATION allocation = CACHE_ALLOC::STORE_ALLOCATE;

typedef CACHE_ROUND_ROBIN(max_sets, max_associativity, allocation) CACHE;
} // namespace DL1

DL1::CACHE* dl1 = NULL;

typedef enum
{
    COUNTER_MISS = 0,
    COUNTER_HIT  = 1,
    COUNTER_NUM
} COUNTER;

typedef COUNTER_ARRAY< UINT64, COUNTER_NUM > COUNTER_HIT_MISS;

// holds the counters with misses and hits
// conceptually this is an array indexed by instruction address
COMPRESSOR_COUNTER< ADDRINT, UINT32, COUNTER_HIT_MISS > profile;

/* ===================================================================== */

// update for every req
VOID UpdateFootPrintPerReq(ADDRINT addr, UINT32 size = 64)
{
    for (ADDRINT addraligned = addr >> 6;(addraligned<<6) < (addr + size);
         addraligned++) {

        if (memFootPrint100M.count(addraligned) == 0)
            memFootPrint100M.insert(addraligned);
    }
}

// NOTICE!!!! This addr is basic addr >> 6
// Thus page addr is >> 6 huge page addr is >> 12
VOID UpdateFullRecord4KB(ADDRINT addr)
{
    ADDRINT pageAligned = addr >> 6;
    ADDRINT pageOffset  = addr & (CACHESIZE-1);
    ADDRINT hugePageAligned = addr >> 12;
    ADDRINT superPageAligned = addr >> 16;

    if (superPageRecord.count(superPageAligned)) {
        return;
    } else if (hugePageRecord.count(hugePageAligned) != 0) {
        return;
    } else if (pageRecord.count(pageAligned) != 0) {
        return;
    } else if (memFootPrint4KB.count(pageAligned) == 0) {
        set<ADDRINT> offSet;
        offSet.insert(pageOffset);
        memFootPrint4KB[pageAligned] = offSet;
        return;
    }

    auto& pageSet = memFootPrint4KB[pageAligned];
    if (pageSet.count(pageOffset) == 0) {
        pageSet.insert(pageOffset);
        // This is a full page
        if (pageSet.size() == 64) {
            pageRecord.insert(pageAligned);
            memFootPrint4KB.erase(pageAligned);
        }
    }
}
// update MemFootPrint and MemFootPrint1B
VOID UpdateFootPrintEvery100M()
{
    for (auto iter = memFootPrint100M.begin();iter != memFootPrint100M.end();iter++) {
        UpdateFullRecord4KB(*iter);
        if (memFootPrint1B.count(*iter) == 0)
            memFootPrint1B.insert(*iter);
    }
}

void UpdateHugePageRecord() {
    map<UINT64,int> procHugePage;
    set<UINT64> mergedPage;
    for (auto iter = pageRecord.begin(); iter != pageRecord.end() ; iter++){
        UINT64 hugePageAddr = *iter >> 6;
        if (procHugePage.count(hugePageAddr)== 0) {
            procHugePage[hugePageAddr] = 1;
        } else {
            procHugePage[hugePageAddr] +=1;
            if (procHugePage[hugePageAddr] == 64) {
                hugePageRecord.insert(hugePageAddr);
                mergedPage.insert(hugePageAddr);
            }
        }
    }

    for (auto iter = mergedPage.begin(); iter != mergedPage.end() ; iter++) {
        for ( UINT64 pageOffset = 0 ; pageOffset < 64; pageOffset++) {
            pageRecord.erase((*iter << 6) +pageOffset);
        }
    }
}

void UpdateSuperPageRecord() {
    map<UINT64,int> procSuperPage;
    set<UINT64> mergedPage;
    for (auto iter = hugePageRecord.begin(); iter != hugePageRecord.end() ; iter++){
        UINT64 superPageAddr = *iter >> 4;
        if (procSuperPage.count(superPageAddr)== 0) {
            procSuperPage[superPageAddr] = 1;
        } else {
            procSuperPage[superPageAddr] +=1;
            if (procSuperPage[superPageAddr] == 16) {
                hugePageRecord.insert(superPageAddr);
                mergedPage.insert(superPageAddr);
            }
        }
    }

    for (auto iter = mergedPage.begin(); iter != mergedPage.end() ; iter++) {
        for ( UINT64 pageOffset = 0 ; pageOffset < 16; pageOffset++) {
            hugePageRecord.erase((*iter << 4) +pageOffset);
        }
    }
}

UINT64 GetFullFootPrint()
{
    UINT64 fullsize = 0;
    fullsize +=superPageRecord.size() * 4096*64*16;
    fullsize +=hugePageRecord.size() * 4096*64;
    fullsize +=pageRecord.size() * 4096;
    for (auto iter = memFootPrint4KB.begin();iter != memFootPrint4KB.end();iter++){
        fullsize += iter->second.size()*64;
    }

    return fullsize;
}

/* ===================================================================== */

VOID LoadMulti(ADDRINT addr, UINT32 size, UINT32 instId)
{
    UpdateFootPrintPerReq(addr,size);
}

/* ===================================================================== */

VOID StoreMulti(ADDRINT addr, UINT32 size, UINT32 instId)
{
    UpdateFootPrintPerReq(addr,size);
}

/* ===================================================================== */

VOID LoadSingle(ADDRINT addr, UINT32 instId)
{
    UpdateFootPrintPerReq(addr);
}
/* ===================================================================== */

VOID StoreSingle(ADDRINT addr, UINT32 instId)
{
    UpdateFootPrintPerReq(addr);
}

/* ===================================================================== */

VOID LoadMultiFast(ADDRINT addr, UINT32 size) {
    UpdateFootPrintPerReq(addr);
}

/* ===================================================================== */

VOID StoreMultiFast(ADDRINT addr, UINT32 size) {
    UpdateFootPrintPerReq(addr,size);
}

/* ===================================================================== */

VOID LoadSingleFast(ADDRINT addr) {
    UpdateFootPrintPerReq(addr);
}

/* ===================================================================== */

VOID StoreSingleFast(ADDRINT addr) {
    UpdateFootPrintPerReq(addr);
}

/* ===================================================================== */

VOID Instruction(INS ins, void* v)
{
    UINT32 memOperands = INS_MemoryOperandCount(ins);

    INS_InsertCall(ins, IPOINT_BEFORE, AFUNPTR(Count100MInst), IARG_END);

    // Instrument each memory operand. If the operand is both read and written
    // it will be processed twice.
    // Iterating over memory operands ensures that instructions on IA-32 with
    // two read operands (such as SCAS and CMPS) are correctly handled.
    for (UINT32 memOp = 0; memOp < memOperands; memOp++)
    {
        const UINT32 size = INS_MemoryOperandSize(ins, memOp);
        const BOOL single = (size <= 4);

        if (INS_MemoryOperandIsRead(ins, memOp))
        {
            if (KnobTrackLoads)
            {
                // map sparse INS addresses to dense IDs
                const ADDRINT iaddr = INS_Address(ins);
                const UINT32 instId = profile.Map(iaddr);

                if (single)
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)LoadSingle, IARG_MEMORYOP_EA, memOp, IARG_UINT32,
                                             instId, IARG_END);
                }
                else
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)LoadMulti, IARG_MEMORYOP_EA, memOp, IARG_UINT32, size,
                                             IARG_UINT32, instId, IARG_END);
                }
            }
            else
            {
                if (single)
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)LoadSingleFast, IARG_MEMORYOP_EA, memOp, IARG_END);
                }
                else
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)LoadMultiFast, IARG_MEMORYOP_EA, memOp, IARG_UINT32,
                                             size, IARG_END);
                }
            }
        }

        if (INS_MemoryOperandIsWritten(ins, memOp))
        {
            if (KnobTrackStores)
            {
                const ADDRINT iaddr = INS_Address(ins);
                const UINT32 instId = profile.Map(iaddr);

                if (single)
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)StoreSingle, IARG_MEMORYOP_EA, memOp, IARG_UINT32,
                                             instId, IARG_END);
                }
                else
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)StoreMulti, IARG_MEMORYOP_EA, memOp, IARG_UINT32, size,
                                             IARG_UINT32, instId, IARG_END);
                }
            }
            else
            {
                if (single)
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)StoreSingleFast, IARG_MEMORYOP_EA, memOp, IARG_END);
                }
                else
                {
                    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)StoreMultiFast, IARG_MEMORYOP_EA, memOp, IARG_UINT32,
                                             size, IARG_END);
                }
            }
        }
    }
}

/* ===================================================================== */

VOID WriteIntoInfoVec() {
    FootPrintInfo footPrintInfo;

    UINT64 memFootInc = GetFullFootPrint() - memFootLen;
    memFootLen = GetFullFootPrint();

    footPrintInfo.currFoot = GetFullFootPrint();
    footPrintInfo.increase = memFootInc;
    footPrintInfo.recent100MFoot = memFootPrint100M.size()*64;

    infoVec.push_back(footPrintInfo);
}

VOID PrintInfo(UINT64 instCnter,FootPrintInfo& footInfo)
{
    file_out << "# InstCnt: " << instCnter << std::endl;

    file_out << "@ footprint current " << std::dec << footInfo.currFoot << std::endl;
    file_out << "@ footprint increase " << footInfo.increase << std::endl;
    file_out << "@ Recent 100M inst footprint " << footInfo.recent100MFoot << std::endl;
}

VOID PrintInfo()
{
    file_out << "# InstCnt: " << instCnter << std::endl;

    // show foot print
    UINT64 memFootInc = GetFullFootPrint() - memFootLen;
    file_out << "@ footprint current " << std::dec << GetFullFootPrint() << std::endl;
    file_out << "@ footprint increase " << memFootInc << std::endl;
    memFootLen = GetFullFootPrint();

    // show foot print
    UINT64 recentFootLen = memFootPrint100M.size();
    file_out << "@ Recent 100M inst footprint " << recentFootLen*64 << std::endl;

    memFootPrint100M.clear();
}

VOID PrintPageInfo()
{
    file_out << "---------------------------------" << std::endl;
    file_out << "superPage " << superPageRecord.size() << "hugePage " <<
    hugePageRecord.size() << " page " << pageRecord.size() << std::endl;

    for(auto iter = hugePageRecord.begin(); iter != hugePageRecord.end(); iter++) {
        ADDRINT addr = *iter << 18;
        file_out << "@@ huge page addr " << std::hex << addr << std::endl;
    }

    for(auto iter = pageRecord.begin(); iter != pageRecord.end(); iter++) {
        ADDRINT addr = *iter << 12;
        file_out << "@@ page addr " << std::hex << addr << std::endl;
    }

    for (auto iter = memFootPrint4KB.begin(); iter != memFootPrint4KB.end(); iter++) {
        auto& footSet = iter->second;
        for (auto offsetIter = footSet.begin(); offsetIter!=footSet.end(); offsetIter++)         {
            file_out << "@@ page addr " << std::hex << iter->first
            << " offset " << std::hex << *offsetIter << std::endl;
        }
    }
}

VOID Fini(int code, VOID* v)
{

}

/* ===================================================================== */

int main(int argc, char* argv[])
{
    PIN_InitSymbols();

    if (PIN_Init(argc, argv))
    {
        return Usage();
    }

    // open file
    std::string fileName(KnobOutputFile.Value().c_str());
    file_out.open(fileName,std::ios_base::app);

    INS_AddInstrumentFunction(Instruction, 0);
    PIN_AddFiniFunction(Fini, 0);

    // Never returns

    PIN_StartProgram();

    return 0;
}

static void Count100MInst() {
    instCnter++;
    // print footprint info every 100M
    if (instCnter % 100000000 == 0) {
        UpdateFootPrintEvery100M();
        WriteIntoInfoVec();
        memFootPrint100M.clear();
        //PrintInfo();
    }

    // reset mem foot print for 1B
    if (instCnter % 1000000000 == 0) {
        UpdateHugePageRecord();
        // output history infoVec
        // We can do this every 100M. Moving to here will save sim time.
        for (UINT64 i = 0; i < infoVec.size(); i++){
            UINT64 instCnt = (int(instCnter/100000000) - infoVec.size() + i)*100000000;
            PrintInfo(instCnt,infoVec[i]);
        }
        infoVec.clear();

        // show foot print
        UINT64 recentFootLen = memFootPrint1B.size();
        file_out << "@ Recent 1B inst footprint " << recentFootLen*64 << std::endl;

        memFootPrint1B.clear();
    }

    // save some time 600B is enough
    if (instCnter>600000000000)
        exit(0);
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
