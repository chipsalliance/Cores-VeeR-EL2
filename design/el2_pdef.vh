//********************************************************************************
// SPDX-License-Identifier: Apache-2.0
// Copyright 2020 Western Digital Corporation or its affiliates.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//********************************************************************************


typedef struct packed {
	logic [7:0]      BHT_ADDR_HI;
	logic [5:0]      BHT_ADDR_LO;
	logic [14:0]     BHT_ARRAY_DEPTH;
	logic [4:0]      BHT_GHR_HASH_1;
	logic [7:0]      BHT_GHR_SIZE;
	logic [15:0]     BHT_SIZE;
	logic [4:0]      BITMANIP_ZBA;
	logic [4:0]      BITMANIP_ZBB;
	logic [4:0]      BITMANIP_ZBC;
	logic [4:0]      BITMANIP_ZBE;
	logic [4:0]      BITMANIP_ZBF;
	logic [4:0]      BITMANIP_ZBP;
	logic [4:0]      BITMANIP_ZBR;
	logic [4:0]      BITMANIP_ZBS;
	logic [8:0]      BTB_ADDR_HI;
	logic [5:0]      BTB_ADDR_LO;
	logic [12:0]     BTB_ARRAY_DEPTH;
	logic [4:0]      BTB_BTAG_FOLD;
	logic [8:0]      BTB_BTAG_SIZE;
	logic [4:0]      BTB_ENABLE;
	logic [4:0]      BTB_FOLD2_INDEX_HASH;
	logic [4:0]      BTB_FULLYA;
	logic [8:0]      BTB_INDEX1_HI;
	logic [8:0]      BTB_INDEX1_LO;
	logic [8:0]      BTB_INDEX2_HI;
	logic [8:0]      BTB_INDEX2_LO;
	logic [8:0]      BTB_INDEX3_HI;
	logic [8:0]      BTB_INDEX3_LO;
	logic [13:0]     BTB_SIZE;
	logic [8:0]      BTB_TOFFSET_SIZE;
	logic [4:0]      BUILD_AHB_LITE;
	logic            BUILD_AXI4;
	logic [4:0]      BUILD_AXI_NATIVE;
	logic [5:0]      BUS_PRTY_DEFAULT;
	logic [35:0]     DATA_ACCESS_ADDR0;
	logic [35:0]     DATA_ACCESS_ADDR1;
	logic [35:0]     DATA_ACCESS_ADDR2;
	logic [35:0]     DATA_ACCESS_ADDR3;
	logic [35:0]     DATA_ACCESS_ADDR4;
	logic [35:0]     DATA_ACCESS_ADDR5;
	logic [35:0]     DATA_ACCESS_ADDR6;
	logic [35:0]     DATA_ACCESS_ADDR7;
	logic [4:0]      DATA_ACCESS_ENABLE0;
	logic [4:0]      DATA_ACCESS_ENABLE1;
	logic [4:0]      DATA_ACCESS_ENABLE2;
	logic [4:0]      DATA_ACCESS_ENABLE3;
	logic [4:0]      DATA_ACCESS_ENABLE4;
	logic [4:0]      DATA_ACCESS_ENABLE5;
	logic [4:0]      DATA_ACCESS_ENABLE6;
	logic [4:0]      DATA_ACCESS_ENABLE7;
	logic [35:0]     DATA_ACCESS_MASK0;
	logic [35:0]     DATA_ACCESS_MASK1;
	logic [35:0]     DATA_ACCESS_MASK2;
	logic [35:0]     DATA_ACCESS_MASK3;
	logic [35:0]     DATA_ACCESS_MASK4;
	logic [35:0]     DATA_ACCESS_MASK5;
	logic [35:0]     DATA_ACCESS_MASK6;
	logic [35:0]     DATA_ACCESS_MASK7;
	logic [6:0]      DCCM_BANK_BITS;
	logic [8:0]      DCCM_BITS;
	logic [6:0]      DCCM_BYTE_WIDTH;
	logic [9:0]      DCCM_DATA_WIDTH;
	logic [6:0]      DCCM_ECC_WIDTH;
	logic [4:0]      DCCM_ENABLE;
	logic [9:0]      DCCM_FDATA_WIDTH;
	logic [7:0]      DCCM_INDEX_BITS;
	logic [8:0]      DCCM_NUM_BANKS;
	logic [7:0]      DCCM_REGION;
	logic [35:0]     DCCM_SADR;
	logic [13:0]     DCCM_SIZE;
	logic [5:0]      DCCM_WIDTH_BITS;
	logic [6:0]      DIV_BIT;
	logic [4:0]      DIV_NEW;
	logic [6:0]      DMA_BUF_DEPTH;
	logic [8:0]      DMA_BUS_ID;
	logic [5:0]      DMA_BUS_PRTY;
	logic [7:0]      DMA_BUS_TAG;
	logic [4:0]      FAST_INTERRUPT_REDIRECT;
	logic [4:0]      ICACHE_2BANKS;
	logic [6:0]      ICACHE_BANK_BITS;
	logic [6:0]      ICACHE_BANK_HI;
	logic [5:0]      ICACHE_BANK_LO;
	logic [7:0]      ICACHE_BANK_WIDTH;
	logic [6:0]      ICACHE_BANKS_WAY;
	logic [7:0]      ICACHE_BEAT_ADDR_HI;
	logic [7:0]      ICACHE_BEAT_BITS;
	logic [4:0]      ICACHE_BYPASS_ENABLE;
	logic [17:0]     ICACHE_DATA_DEPTH;
	logic [6:0]      ICACHE_DATA_INDEX_LO;
	logic [10:0]     ICACHE_DATA_WIDTH;
	logic [4:0]      ICACHE_ECC;
	logic [4:0]      ICACHE_ENABLE;
	logic [10:0]     ICACHE_FDATA_WIDTH;
	logic [8:0]      ICACHE_INDEX_HI;
	logic [10:0]     ICACHE_LN_SZ;
	logic [7:0]      ICACHE_NUM_BEATS;
	logic [7:0]      ICACHE_NUM_BYPASS;
	logic [7:0]      ICACHE_NUM_BYPASS_WIDTH;
	logic [6:0]      ICACHE_NUM_WAYS;
	logic [4:0]      ICACHE_ONLY;
	logic [7:0]      ICACHE_SCND_LAST;
	logic [12:0]     ICACHE_SIZE;
	logic [6:0]      ICACHE_STATUS_BITS;
	logic [4:0]      ICACHE_TAG_BYPASS_ENABLE;
	logic [16:0]     ICACHE_TAG_DEPTH;
	logic [6:0]      ICACHE_TAG_INDEX_LO;
	logic [8:0]      ICACHE_TAG_LO;
	logic [7:0]      ICACHE_TAG_NUM_BYPASS;
	logic [7:0]      ICACHE_TAG_NUM_BYPASS_WIDTH;
	logic [4:0]      ICACHE_WAYPACK;
	logic [6:0]      ICCM_BANK_BITS;
	logic [8:0]      ICCM_BANK_HI;
	logic [8:0]      ICCM_BANK_INDEX_LO;
	logic [8:0]      ICCM_BITS;
	logic [4:0]      ICCM_ENABLE;
	logic [4:0]      ICCM_ICACHE;
	logic [7:0]      ICCM_INDEX_BITS;
	logic [8:0]      ICCM_NUM_BANKS;
	logic [4:0]      ICCM_ONLY;
	logic [7:0]      ICCM_REGION;
	logic [35:0]     ICCM_SADR;
	logic [13:0]     ICCM_SIZE;
	logic [4:0]      IFU_BUS_ID;
	logic [5:0]      IFU_BUS_PRTY;
	logic [7:0]      IFU_BUS_TAG;
	logic [35:0]     INST_ACCESS_ADDR0;
	logic [35:0]     INST_ACCESS_ADDR1;
	logic [35:0]     INST_ACCESS_ADDR2;
	logic [35:0]     INST_ACCESS_ADDR3;
	logic [35:0]     INST_ACCESS_ADDR4;
	logic [35:0]     INST_ACCESS_ADDR5;
	logic [35:0]     INST_ACCESS_ADDR6;
	logic [35:0]     INST_ACCESS_ADDR7;
	logic [4:0]      INST_ACCESS_ENABLE0;
	logic [4:0]      INST_ACCESS_ENABLE1;
	logic [4:0]      INST_ACCESS_ENABLE2;
	logic [4:0]      INST_ACCESS_ENABLE3;
	logic [4:0]      INST_ACCESS_ENABLE4;
	logic [4:0]      INST_ACCESS_ENABLE5;
	logic [4:0]      INST_ACCESS_ENABLE6;
	logic [4:0]      INST_ACCESS_ENABLE7;
	logic [35:0]     INST_ACCESS_MASK0;
	logic [35:0]     INST_ACCESS_MASK1;
	logic [35:0]     INST_ACCESS_MASK2;
	logic [35:0]     INST_ACCESS_MASK3;
	logic [35:0]     INST_ACCESS_MASK4;
	logic [35:0]     INST_ACCESS_MASK5;
	logic [35:0]     INST_ACCESS_MASK6;
	logic [35:0]     INST_ACCESS_MASK7;
	logic [4:0]      LOAD_TO_USE_PLUS1;
	logic [4:0]      LSU2DMA;
	logic [4:0]      LSU_BUS_ID;
	logic [5:0]      LSU_BUS_PRTY;
	logic [7:0]      LSU_BUS_TAG;
	logic [8:0]      LSU_NUM_NBLOAD;
	logic [6:0]      LSU_NUM_NBLOAD_WIDTH;
	logic [8:0]      LSU_SB_BITS;
	logic [7:0]      LSU_STBUF_DEPTH;
	logic [4:0]      NO_ICCM_NO_ICACHE;
	logic [4:0]      PIC_2CYCLE;
	logic [35:0]     PIC_BASE_ADDR;
	logic [8:0]      PIC_BITS;
	logic [7:0]      PIC_INT_WORDS;
	logic [7:0]      PIC_REGION;
	logic [12:0]     PIC_SIZE;
	logic [11:0]     PIC_TOTAL_INT;
	logic [12:0]     PIC_TOTAL_INT_PLUS1;
	logic [7:0]      RET_STACK_SIZE;
	logic [4:0]      SB_BUS_ID;
	logic [5:0]      SB_BUS_PRTY;
	logic [7:0]      SB_BUS_TAG;
	logic [4:0]      TIMER_LEGAL_EN;
} el2_param_t;

