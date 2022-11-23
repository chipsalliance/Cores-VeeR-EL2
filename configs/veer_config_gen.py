#!/usr/bin/env python3
from fusesoc.capi2.generator import Generator
import os
import subprocess
import sys

class VeerConfigGenerator(Generator):
    def run(self):
        script_root = os.path.abspath(os.path.join(os.path.dirname(sys.argv[0]), '..'))
        files = [
            {"common_defines.vh" : {
                "copyto"    : "config/common_defines.vh",
                "file_type" : "systemVerilogSource"}},
            {"el2_pdef.vh" : {
                "copyto" : "config/el2_pdef.vh",
                "file_type" : "systemVerilogSource"}},
            {"el2_param.vh" : {
                "is_include_file" : True,
                "file_type" : "systemVerilogSource"}},
            {"pic_map_auto.h" : {
                "is_include_file" : True,
                "file_type" : "systemVerilogSource"}}]

        env = os.environ.copy()
        env['RV_ROOT'] = script_root
        env['BUILD_PATH'] = os.getcwd()
        args = ['configs/veer.config'] + self.config.get('args', [])

        rc = subprocess.call(args, cwd=script_root, env=env, stdout=subprocess.DEVNULL)
        if rc:
            exit(1)
        filenames = []
        for f in files:
            for k in f:
                filenames.append(k)

        self.add_files(files)

g = VeerConfigGenerator()
g.run()
g.write()
