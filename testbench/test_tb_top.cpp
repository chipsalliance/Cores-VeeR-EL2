// SPDX-License-Identifier: Apache-2.0
// Copyright 2019 Western Digital Corporation or its affiliates.
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
//
#include <stdlib.h>
#include <iostream>
#include <iomanip>
#include <utility>
#include <string>
#include <fstream>
#include "Vtb_top.h"
#include "verilated.h"
#include "verilated_vcd_c.h"


vluint64_t main_time = 0;

double sc_time_stamp () {
 return main_time;
}

std::map<std::string, uint64_t> load_symbols (const std::string& fileName) {

    // Open the symbol list file
    std::ifstream fp(fileName);
    if (!fp.good()) {
        std::cerr << "Error loading symbols from '" << fileName << "'" << std::endl;
        exit(EXIT_FAILURE);
    }

    // Parse lines
    std::map<std::string, uint64_t> symbols;
    for (std::string line; std::getline(fp, line); ) {

        // Remove any trailing whitespaces
        auto pos = line.find_last_not_of(" \r\n\t");
        line = line.substr(0, pos + 1);

        // Get address
        auto apos = line.find_first_of(" \r\n\t");
        const auto astr = line.substr(0, apos);

        // Get name
        auto npos = line.find_last_of(" \r\n\t");
        const auto nstr = line.substr(npos + 1);

        symbols[nstr] = strtol(astr.c_str(), nullptr, 16);
    }

    return symbols;
}

int main(int argc, char** argv) {
  std::cout << "\nVerilatorTB: Start of sim\n" << std::endl;

  Verilated::commandArgs(argc, argv);

  Vtb_top* tb = new Vtb_top;

  tb->mem_signature_begin = 0x00000000;
  tb->mem_signature_end   = 0x00000000;
  tb->mem_mailbox         = 0xD0580000;

  std::map<std::string, uint64_t> symbols;

  // Setup memory signature range by looking up symbol names in the provided
  // symbol dump file
  for (int i=1; i<argc; ++i) {
    if (!strcmp(argv[i], "--symbols") && (i + 1) < argc) {
      symbols = load_symbols(argv[i+1]);

      const auto beg = symbols.find("begin_signature");
      const auto end = symbols.find("end_signature");
      if (beg != symbols.end() && end != symbols.end()) {
        tb->mem_signature_begin = beg->second;
        tb->mem_signature_end   = end->second;
      }
    }
  }

  // Setup memory signature range if provided. Look for the commandline option
  // "--mem-signature <begin> <end>". Addresses need to be hexadecimal
  for (int i=1; i<argc; ++i) {
    if (!strcmp(argv[i], "--mem-signature") && (i + 2) < argc) {
      tb->mem_signature_begin = strtol(argv[i+1], nullptr, 16);
      tb->mem_signature_end   = strtol(argv[i+2], nullptr, 16);
    }
  }

  // Set mailbox address if provided. The commandline option is:
  // "--mailbox-addr <address>"
  for (int i=1; i<argc; ++i) {
    if (!strcmp(argv[i], "--mailbox-addr") && (i + 1) < argc) {
      tb->mem_mailbox = strtol(argv[i+1], nullptr, 16);
    }
  }

  // Set mailbox address to the address of the given symbol name via:
  // "--mailbox-sym <symbol name>"
  for (int i=1; i<argc; ++i) {
    if (!strcmp(argv[i], "--mailbox-sym") && (i + 1) < argc) {
      const char* name = argv[i+1];
      auto it = symbols.find(name);
      if (it != symbols.end()) {
        tb->mem_mailbox = it->second;
      }
    }
  }

  // Report memory addresses
  std::cout << std::setfill('0');

  std::cout << "mem_signature_begin = " << std::hex << std::setw(8) <<
    std::uppercase << tb->mem_signature_begin << std::endl;
  std::cout << "mem_signature_end   = " << std::hex << std::setw(8) <<
    std::uppercase << tb->mem_signature_end   << std::endl;
  std::cout << "mem_mailbox         = " << std::hex << std::setw(8) <<
    std::uppercase << tb->mem_mailbox         << std::endl;
  std::cout << std::flush;

  // init trace dump
  VerilatedVcdC* tfp = NULL;

#if VM_TRACE
  Verilated::traceEverOn(true);
  tfp = new VerilatedVcdC;
  tb->trace (tfp, 24);
  tfp->open ("sim.vcd");
#endif
  // Simulate
  while(!Verilated::gotFinish()){
#if VM_TRACE
      tfp->dump (main_time);
#endif
      main_time += 5;
      tb->core_clk = !tb->core_clk;
      tb->eval();
  }
  tb->final();

#if VM_TRACE
  tfp->close();
#endif

  // Write coverage data
#if VM_COVERAGE
  Verilated::threadContextp()->coveragep()->write("coverage.dat");
#endif

  std::cout << "\nVerilatorTB: End of sim" << std::endl;
  exit(EXIT_SUCCESS);

}
