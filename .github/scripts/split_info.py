import sys
files = {}
active_file = None
with open(sys.argv[1], 'r') as file:
 for line in file:
   if line[0:1] == "#":
       continue
   elif line[0:3] == "SF:":
       active_file = line.replace("\n", "").split(":")[1]
       files[active_file] = {}
       files[active_file]["da"] = []
       files[active_file]["brda"] = []
       files[active_file]["brf"] = 0
       files[active_file]["brh"] = 0
   elif line[0:3] == "DA:":
       files[active_file]["da"].append(line.replace("\n", "").split(":")[1:])
   elif line[0:5] == "BRDA:":
       files[active_file]["brda"].append(line.replace("\n", "").split(":")[1:])
   elif line[0:4] == "BRF:":
       files[active_file]["brf"] = int(line.replace("\n", "").split(":")[1])
   elif line[0:4] == "BRH:":
       files[active_file]["brh"] = int(line.replace("\n", "").split(":")[1])
   elif "end_of_record" in line:
       active_file = None
if sys.argv[2] == "--branch":
  print("TN:verilator_coverage")
  for f in files:
     print("SF:%s" % f)
     for brda in files[f]["brda"]:
       brda_line = brda[0].split(",")[0]
       for da in files[f]["da"]:
          da_line = da[0].split(",")[0]
          if da_line == brda_line:
            print("DA:%s" % (",".join(da)))
            files[f]["da"].remove(da)
       print("BRDA:%s" % (",".join(brda)))
     print("end_of_record")
elif sys.argv[2] == "--line":
  print("TN:verilator_coverage")
  for f in files:
     print("SF:%s" % f)
     for da in files[f]["da"]:
       print("DA:%s" % (",".join(da)))
     print("end_of_record")
  sys.exit(0)
