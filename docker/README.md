## Getting Started

This project includes a Dockerfile that automatically clones and builds Z3, copies the MultiTheoryHorn source code, and builds it inside the container.  
After a successful build, the working directory inside the container will be set to our project's root: `/MultiTheoryHorn`.

## Building the Docker Container

To build the Docker container, run the following command from the project's root (/MultiTheoryHorn):
```
docker build -t mth/review -f docker/Dockerfile .
```
**Note:** Building Z3 can be time-consuming, as it is a large project. The majority of the build time will be spent on building Z3.

## Running the Docker Container

Once the Docker build process is complete, you can start the container with:
```
docker run -it mth/review
```

## Benchmarks Binary

The compiled C++ benchmarks binary is located at `/MultiTheoryHorn/build/bin/benchmarks` inside the container.

To view all available command-line options for the benchmarks binary, run:
```
./build/bin/benchmarks --help
```

To list all enabled benchmarks, use:
```
./build/bin/benchmarks --list
```

### Basic Usage

To run a specific benchmark with a given bit-vector size:
```
./build/bin/benchmarks --bench <bench_name> --size <bit_vector_size>
```

**Example:**
```
./build/bin/benchmarks --bench max_multi --size 4
```

You can reproduce standalone benchmark runs with a specific bit-vector size using the above command.  
For additional logging, use the `--debug` flag together with the `--output` flag to save debug logs to a file:
```
./build/bin/benchmarks --bench max_multi --size 4 --debug --output dbg.out
```

## Provided Scripts

The `MultiTheoryHorn/ext` directory contains scripts to automate running the enabled benchmarks. The main script being `ext/get_files.sh`, which can be customized to control the benchmark runs.

Within `ext/get_files.sh`, you will find several configuration variables. The file's contents are set to reproduce the logs provided with the artifact. But for quick review or testing, we recommend adjusting the following settings:
```
TIMEOUT=7200
MEMOUT=16384
SIZE_MIN=4
SIZE_MAX=5 # <-- (CHANGE HERE)
SIZE_STEP=1
DEBUG=true
```
Here, only `SIZE_MAX` is changed from its default (64) to 5, significantly reducing the runtime. You can edit this file using editors like `vim` or `nano`.

The script can be run as follows:
```
./ext/get_files.sh
```

After the script finishes, results and logs will be available in a newly created directory: `MultiTheoryHorn/out`. This directory contains all logs and statistics from the benchmark runs.

To aggregate all statistics into a single `.csv` file, use the provided script:
```
./ext/generate_csv.sh out/benchmarks_<invocation_date>/stats/header.csv
```
Replace `<invocation_date>` with the actual date of your benchmark run.
An inclusive `results.csv` file will be created in:
```
out/benchmarks_<invocation_date>/stats/results.csv
```