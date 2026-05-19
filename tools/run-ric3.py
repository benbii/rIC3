#!/usr/bin/env python3
import argparse
import os
import random
import sys
import tempfile
from datetime import datetime
from pathlib import Path


parser = argparse.ArgumentParser()
parser.add_argument("-i", "--inputdir", required=True)
parser.add_argument("-w", "--workers", type=int, default=os.cpu_count() or 1)
parser.add_argument("-m", "--mode", "--preset", dest="preset", required=True)
parser.add_argument("-t", "--timeout", type=int, default=3600)
parser.add_argument("-M", "--memory", type=int, default=6500000)
parser.add_argument("-n", "--numa", type=int, default=0)
parser.add_argument("-s", "--solver")
parser.add_argument("-r", "--run-info")
parser.add_argument("-o", "--out", "--basename", dest="log_basename")
parser.add_argument("-a", "--listen-addr")
parser.add_argument("-p", "--listen-port")
parser.add_argument("-S", "--secret")
args = parser.parse_args()

script_dir = Path(__file__).resolve().parent
run_info = Path(args.run_info).resolve() if args.run_info else script_dir / "run-info"
inputdir = Path(args.inputdir).resolve()
ymdHMS = datetime.now().strftime("%y%m%d%H%M%S")
log_basename = Path(args.log_basename if args.log_basename else f"{ymdHMS}-{args.preset}").resolve()
logsmall = Path(str(log_basename) + ".txt")
loglarge = Path(str(log_basename) + ".md")
solver = args.solver
if solver is None:
  solver = "abc" if args.preset.startswith("abc") else "ric3"

# Each command template is argv without the testcase. TESTCASE is inserted after
# "check" for ric3 presets and inside the ABC -c string for ABC presets below.
bmc1 = [solver, "check", "TESTCASE", "bmc", "--step", "1", "--rseed", "12"]
bmc10 = [solver, "check", "TESTCASE", "bmc", "--kissat", "--step", "10", "--rseed", "13"]
bmc65 = [solver, "check", "TESTCASE", "bmc", "--kissat", "--step", "65", "--rseed", "14"]
bmc_dyn = [solver, "check", "TESTCASE", "bmc", "--kissat", "--dyn-step", "--rseed", "15"]
ic3_basic = [solver, "check", "TESTCASE", "ic3", "--rseed", "1"]
ic3_no_ctg = [
  solver, "check", "TESTCASE", "ic3", "--ctg=false", "--frts=false",
  "--scorr=false", "--drop-po=false", "--rseed", "2",
]
ic3_no_drop = [
  solver, "check", "TESTCASE", "ic3", "--drop-po=false",
  "--parent-lemma=false", "--rseed", "3",
]
ic3_abs_cst = [solver, "check", "TESTCASE", "ic3", "--abs-cst", "--rseed", "4"]
ic3_abs_cst_trans = [
  solver, "check", "TESTCASE", "ic3", "--abs-cst", "--abs-trans", "--rseed", "5",
]
ic3_pred_prop = [solver, "check", "TESTCASE", "ic3", "--pred-prop", "--rseed", "6"]
ic3_ctg = [
  solver, "check", "TESTCASE", "ic3", "--ctg-max", "5",
  "--ctg-limit", "15", "--drop-po=false", "--rseed", "7",
]
ic3_inn = [solver, "check", "TESTCASE", "ic3", "--inn", "--rseed", "8"]
ic3_inn_ctp = [solver, "check", "TESTCASE", "ic3", "--inn", "--ctp", "--rseed", "9"]
ic3_inn_no_ctg = [solver, "check", "TESTCASE", "ic3", "--inn", "--ctg=false", "--rseed", "10"]
ic3_inn_dyn = [
  solver, "check", "TESTCASE", "ic3", "--inn", "--dynamic",
  "--drop-po=false", "--rseed", "11",
]
kind = [solver, "check", "TESTCASE", "kind", "--rseed", "17"]
kind_simple = [solver, "check", "TESTCASE", "kind", "--simple-path", "--rseed", "16"]

all_commands = [
  bmc1, ic3_basic,
  bmc10 + ["--kissat"], ic3_ctg, ic3_no_ctg, ic3_no_drop,
  bmc65 + ["--kissat"], ic3_abs_cst, ic3_abs_cst_trans,
  bmc_dyn + ["--kissat"], ic3_pred_prop,
  kind_simple, ic3_inn, ic3_inn_ctp, ic3_inn_no_ctg, ic3_inn_dyn,
]
bmc_commands = [
  bmc1, bmc1 + ["--kissat"],
  bmc10, bmc10 + ["--kissat"],
  bmc65, bmc65 + ["--kissat"],
  bmc_dyn, bmc_dyn + ["--kissat"],
]
ic3_commands = [
  ic3_basic,
  ic3_ctg, ic3_no_ctg, ic3_no_drop,
  ic3_abs_cst, ic3_abs_cst_trans,
  ic3_pred_prop,
  ic3_inn, ic3_inn_ctp, ic3_inn_no_ctg, ic3_inn_dyn,
]
kind_commands = [kind, kind_simple]
ic3_basic = ic3_basic[:-1]
ic3_basic_commands = [
  ic3_basic + ["11111111"],
  ic3_basic + ["22222222"],
  ic3_basic + ["33333333"],
  ic3_basic + ["44444444"],
  ic3_basic + ["55555555"],
  ic3_basic + ["66666666"],
]

if args.preset == "all":
  cfg = [[cmd] for cmd in all_commands]
elif args.preset in ("all-portfolio", "all-ptfl"):
  cfg = [all_commands]
elif args.preset == "bmcOnly":
  cfg = [[cmd] for cmd in bmc_commands]
elif args.preset in ("bmcOnly-portfolio", "bmcOnly-ptfl"):
  cfg = [bmc_commands]
elif args.preset == "ic3Only":
  cfg = [[cmd] for cmd in ic3_commands]
elif args.preset in ("ic3Only-portfolio", "ic3Only-ptfl"):
  cfg = [ic3_commands]
elif args.preset == "kind":
  cfg = [[cmd] for cmd in kind_commands]
elif args.preset in ("kind-portfolio", "kind-ptfl"):
  cfg = [kind_commands]
elif args.preset in ("basic", "ic3Basic"):
  cfg = [[cmd] for cmd in ic3_basic_commands]
elif args.preset in ("basic-portfolio", "basic-ptfl", "ic3Basic-portfolio", "ic3Basic-ptfl"):
  cfg = [ic3_basic_commands]

elif args.preset == "abcLcorr":
  cfg = [[[solver, "-c", "read_aiger TESTCASE; lcorr -v; ps"]],
    [[solver, "-c", "read_aiger TESTCASE; lcorr -n -v; ps"]]]
  # [[[solver, "-c", "read_aiger TESTCASE; ps; lcorr -v; ps; dfraig -rc; ps"]]]
elif args.preset == "abcPdr":
  cfg = [[[solver, "-c", "read_aiger TESTCASE; ps; lcorr -v; ps; dfraig; ps; pdr -v"]]]
else:
  sys.exit("unknown preset; read the script for a list (it's easy!)")

testcases = []
for path in inputdir.rglob("*"):
  if path.is_file() and path.suffix in (".aig", ".btor"):
    testcases.append(path.resolve().as_posix())
random.Random(12345678).shuffle(testcases)
if len(testcases) == 0:
  sys.exit(f"no .aig or .btor files found in {inputdir}")
print(f'found {len(testcases)} testcases')

tmp = tempfile.NamedTemporaryFile(prefix="localRunRic3", delete=False)
for testcase in testcases:
  for group in cfg:
    for cmd in group:
      for arg in cmd:
        arg = arg.replace("TESTCASE", testcase)
        tmp.write(arg.encode())
        tmp.write(b"\0")
      tmp.write(b"\0")
    tmp.write(b"\0")
tmp.close()

if (args.listen_addr is None) != (args.listen_port is None):
  sys.exit("--listen-addr and --listen-port must be specified together")

if args.listen_addr is None:
  os.execv(
    str(run_info),
    [
      str(run_info),
      "local",
      "-w", str(args.workers),
      "-t", str(args.timeout),
      "-m", str(args.memory),
      "-n", str(args.numa),
      "-l", str(logsmall),
      "-L", str(loglarge),
      tmp.name,
    ],
  )

submit_argv = [
  str(run_info),
  "submit",
  args.listen_addr,
  args.listen_port,
  tmp.name,
]
if args.secret is not None:
  submit_argv.append(args.secret)
os.execv(str(run_info), submit_argv)
