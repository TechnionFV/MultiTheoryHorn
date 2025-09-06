#!/usr/bin/env python

import os
import os.path
import sys
import csv

def isexec (fpath):
    if fpath == None: return False
    return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

def which(program):
    fpath, fname = os.path.split(program)
    if fpath:
        if isexec (program):
            return program
    else:
        for path in os.environ["PATH"].split(os.pathsep):
            exe_file = os.path.join(path, program)
            if isexec (exe_file):
                return exe_file
    return None

def parseArgs (argv):
    import argparse as a
    p = a.ArgumentParser (description='Benchmark Runner')

    p.add_argument ('--cpu', metavar='CPU',
                    type=int, help='CPU limit', default=60)
    p.add_argument ('--mem', metavar='MEM',
                    type=int, help='Memory limit (MB)', default=512)
    # In our usage this is NOT a file path; it is either "bench:size", "bench,size" or "bench size".
    p.add_argument ('file', nargs='+',
                    help='Benchmark spec(s): bench:size or bench,size or "bench size", or a .list with one spec per line')
    p.add_argument ('--prefix', default='BRUNCH_STAT',
                    help='Prefix for stats')
    p.add_argument ('--format', required=True, help='Fields')

    p.add_argument ('--out', metavar='DIR',
                    default="out", help='Output directory')

    if '-h' in argv or '--help' in argv:
        p.print_help ()
        p.exit (0)

    try:
        k = argv.index ('--')
    except ValueError:
        p.error ("No '--' argument")

    args = p.parse_args (argv[:k])
    args.tool_args = argv[k+1:]

    return args

def collectStats (stats, file, prefix='BRUNCH_STAT'):
    f = open (file, 'r')
    for line in f:
        if not line.startswith (prefix): continue
        fld = line.split (' ')
        if len (fld) == 3:
            stats [fld[1]] = fld[2].strip ()
    f.close ()
    return stats

def statsHeader (stats_file, flds):
    with open (stats_file, 'w') as sf:
        writer = csv.writer (sf)
        writer.writerow (flds)

def statsLine (stats_file, fmt, stats):
    line = list()
    for fld in fmt:
        if fld in stats: line.append (str (stats [fld]))
        else: line.append (None)

    with open (stats_file, 'a') as sf:
        writer = csv.writer (sf)
        writer.writerow (line)

cpuTotal = 0.0


### parse a spec token into (bench, size). Accept "bench:size", "bench,size", or "bench size".
def parse_spec(spec):
    # Normalize separators: space(s), comma, or colon
    s = spec.strip()
    if not s:
        raise ValueError("empty benchmark spec")
    # try colon
    if ':' in s:
        name, sz = s.split(':', 1)
    elif ',' in s:
        name, sz = s.split(',', 1)
    else:
        parts = s.split()
        if len(parts) == 2:
            name, sz = parts[0], parts[1]
        elif len(parts) == 1:
            raise ValueError(f"size missing in spec '{spec}' (use 'bench:size')")
        else:
            raise ValueError(f"cannot parse spec '{spec}'")
    name = name.strip()
    sz = sz.strip()
    if not name or not sz:
        raise ValueError(f"bad spec '{spec}'")
    size_int = int(sz)  # may raise ValueError → caller handles
    base = f"{name}-{size_int}"
    return name, size_int, base

### ensure directories exist: <out>/tool and <out>/stats
def ensure_dirs(out_dir):
    if not os.path.exists(out_dir):
        os.mkdir(out_dir)
    tool_dir = os.path.join(out_dir, 'tool')
    stats_dir = os.path.join(out_dir, 'stats')
    if not os.path.exists(tool_dir):
        os.mkdir(tool_dir)
    if not os.path.exists(stats_dir):
        os.mkdir(stats_dir)
    return tool_dir, stats_dir

def runTool (tool_args, bench, size, base, out, cpu, mem, fmt, prefix='BRUNCH_STAT', results_csv=None):
    global cpuTotal
    import resource as r

    def set_limits ():
        # Best-effort: on macOS RLIMIT_AS often raises; try RLIMIT_DATA as fallback.
        # If anything fails, skip that limit instead of crashing the child.
        if mem > 0:
            mem_bytes = mem * 1024 * 1024
            try:
                if hasattr(r, 'RLIMIT_AS'):
                    r.setrlimit(r.RLIMIT_AS, (mem_bytes, mem_bytes))
                elif hasattr(r, 'RLIMIT_DATA'):
                    r.setrlimit(r.RLIMIT_DATA, (mem_bytes, mem_bytes))
            except Exception:
                # macOS commonly throws here; ignore so the tool still runs.
                pass
        if cpu > 0:
            try:
                r.setrlimit(r.RLIMIT_CPU, (cpu, cpu))
            except Exception:
                pass

    # Allow placeholders in tool args
    fmt_tool_args = [v.format(f=base, bench=bench, size=size) for v in tool_args]
    fmt_tool_args[0] = which (fmt_tool_args[0])  # resolve binary path
    if fmt_tool_args[0] is None:
        raise FileNotFoundError(f"Cannot find executable '{tool_args[0]}' on PATH")

    outfile   = os.path.join(out, 'tool',  base + '.stdout')
    statsfile = os.path.join(out, 'stats', base + '.stats')

    import subprocess as sub
    p = sub.Popen(
        fmt_tool_args,
        stdout=open(outfile, 'w'),
        stderr=sub.STDOUT,
        preexec_fn=set_limits  # OK now: failures are handled inside
    )

    p.wait ()
    cpuUsage = r.getrusage (r.RUSAGE_CHILDREN).ru_utime

    import signal
    result = 'TO' if -p.returncode == signal.SIGXCPU else ('OK' if p.returncode == 0 else 'ERROR')

    stats = dict()
    # Some common fields users often include in --format
    stats['base']   = base
    stats['bench']  = bench
    stats['type']   = 'MULTI' if 'multi' in bench.lower() else 'BV'
    stats['size']   = size
    stats['result'] = result
    stats['Status'] = p.returncode
    stats['Cpu']    = '{0:.2f}'.format (cpuUsage - cpuTotal)
    cpuTotal = cpuUsage

    # Merge BRUNCH_STAT lines (bench/size/result) if present
    stats = collectStats (stats, outfile, prefix=prefix)

    statsLine (statsfile, fmt, stats)
    if results_csv is not None:
        statsLine (results_csv, fmt, stats)

def main (argv):
    args = parseArgs (argv[1:])

    # Prepare dirs
    tool_dir, stats_dir = ensure_dirs(args.out)

    fmt = args.format.split (':')

    # Unified results CSV (header written once if missing)
    results_csv = os.path.join (args.out, 'stats', 'benchmarks_results.csv')
    if not os.path.exists(results_csv):
        statsHeader (results_csv, fmt)

    global cpuTotal
    import resource as r
    cpuTotal = r.getrusage (r.RUSAGE_CHILDREN).ru_utime

    # Expand the positional "file" args:
    # - If it ends with .list, read lines; each line is a spec "bench:size"
    # - Else, treat it as a single spec "bench:size"
    specs = []
    for token in args.file:
        if token.endswith('.list') and os.path.exists(token):
            with open(token, 'r') as F:
                for line in F:
                    line = line.strip()
                    if not line or line.startswith('#'):  # allow comments/blank lines
                        continue
                    specs.append(line)
        else:
            specs.append(token)

    # Run all specs
    for spec in specs:
        try:
            bench, size, base = parse_spec(spec)
        except Exception as e:
            # Record an error row for this spec (per-run and unified)
            base = spec.replace('/', '_').replace(' ', '_')
            statsfile = os.path.join (args.out, 'stats', f"{base}.stats")
            stats = dict()
            stats['base']   = base
            stats['bench']  = 'PARSE_ERROR'
            stats['type']   = ''
            stats['size']   = ''
            stats['result'] = 'ERROR'
            stats['Status'] = 3
            stats['Cpu']    = '0.00'
            statsLine (statsfile, fmt, stats)
            statsLine (results_csv, fmt, stats)
            continue

        runTool (args.tool_args, bench, size, base, args.out,
                 cpu=args.cpu,
                 mem=args.mem,
                 fmt=fmt,
                 prefix=args.prefix,
                 results_csv=results_csv)

    return 0

if __name__ == '__main__':
    sys.exit (main (sys.argv))
