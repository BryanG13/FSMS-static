# FSMS-static: Flexible Service on Mandatory Stops

A C++ optimization solver for dynamic bus routing with mandatory and optional stops, designed to minimize travel time, walking time, and schedule deviations for passenger requests. The code is used in this [academic paper](https://doi.org/10.1002/net.22185).

## Overview

This project implements a Large Neighborhood Search (LNS) metaheuristic to solve the **Flexible Service on Mandatory Stops** problem. The system dynamically assigns buses to passenger requests while:

- Visiting all mandatory stops in sequence
- Selectively visiting optional stops based on passenger demand
- Respecting bus capacity, frequency constraints, and time windows
- Minimizing a weighted objective combining bus travel time, passenger walking time, and schedule deviations

## Problem Description

**Given:**
- A fleet of **B** buses with capacity **C**
- **N** mandatory bus stops (fixed sequence)
- **M** optional stops per cluster (between each pair of mandatory stops)
- **R** passenger requests with:
  - Desired arrival times (for passengers going to a destination)
  - Desired departure times (for passengers leaving from a location)
  - Walking distance tolerance

**Find:**
- Bus routes (which optional stops to visit)
- Timetables for each bus trip
- Passenger-to-bus assignments

**Such that:**
- All mandatory stops are visited by each bus
- Passengers walk at most `dw` seconds to their nearest bus stop
- Frequency constraints are satisfied (minimum headway between buses at mandatory stops)
- Arrival/departure time deviations are within acceptable bounds
- Total weighted cost is minimized

## Features

- **Multi-objective optimization** with configurable weight factors (c1, c2, c3)
- **Parallel processing** with OpenMP support
- **AddressSanitizer instrumentation** for memory safety (Debug builds)
- **Adaptive heuristics** with randomized parameters (pm1, pm2, pm3, fpm, xt, C)
- **Greedy insertion** and **local search** for route construction
- **Flexible input data** format for different problem instances

## Requirements

### System Dependencies

- **C++17** compatible compiler
- **CMake** 3.22 or higher
- **OpenMP** (optional, for parallel execution)
  - macOS: `brew install libomp`
  - Linux: Usually pre-installed with GCC
- **AddressSanitizer** (enabled in Debug mode)

### Build Tools

- macOS: Xcode Command Line Tools or Clang
- Linux: GCC/G++ or Clang
- Windows: MSVC 2019+ or MinGW-w64

## Installation

### Clone the Repository

```bash
git clone https://github.com/BryanG13/FSMS-static.git
cd FSMS-static
```

### Install Dependencies (macOS)

```bash
# Install Homebrew if not already installed
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

# Install OpenMP (optional, for parallel execution)
brew install libomp
```

### Build the Project

```bash
# Configure with CMake
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release

# Build
cmake --build build --config Release -j 8
```

For **Debug** builds with AddressSanitizer (recommended for development):

```bash
cmake -S . -B build -DCMAKE_BUILD_TYPE=Debug
cmake --build build --config Debug -j 8
```

## Usage

### Input Data Structure

Create input files in `Data/input/` (or modify paths in `main.cpp`):

```
Data/input/
├── passengers48.txt      # Passenger locations (x, y coordinates)
├── mandatory.txt         # Mandatory stop locations
├── optional5.txt         # Optional stop locations per cluster
├── arrivals48.txt        # Desired arrival times (first R1 passengers)
└── departures48.txt      # Desired departure times (last R2 passengers)
```

**Format:** Each file contains space-separated values:
- Location files: `x y` coordinates (one per line)
- Time files: `time_in_seconds` (one per line)

### Run the Solver

```bash
./build/FSMS
```

### Output

The solver generates:
- **Console output:** Progress, solution quality, runtime statistics
- **Instance file:** `Instance_H_<instance_id>.txt` with problem parameters
- **Best solution details:** Routes, timetables, passenger assignments

Example output:
```
++++++++++++++++++++++++++++++++++++++ INSTANCE 1 ++++++++++++++++++++++++++++++++++++++++++++++++
0 0 4 5 6 7 8 1 9 10 11 12 13 2 14 15 16 17 18 3 
Time big route: 45 min
Time short route: 32 min

BEST: 
+++++++++++++ COST: 12345.67   Runtime: 123.45
Average Cost: 13000.50   Average RT: 130.25
```

## Configuration

### Problem Parameters

Edit `main.cpp` to adjust:

```cpp
const int B = 12;           // Number of buses
const int N = 6;            // Mandatory stops
const int M = 5;            // Optional stops per cluster
const int R = 48;           // Passenger requests
const int C_OG = 20;        // Bus capacity
const int TS = 3600 * 4.2;  // Planning horizon (seconds)
const int OGxt = 60 * 20;   // Minimum headway (seconds)
const int dw = 20 * 60;     // Max walking time (seconds)

// Weight factors
float c1 = 0.33f;  // Bus travel time
float c2 = 0.33f;  // Passenger walking time
float c3 = 0.34f;  // Schedule deviation
```

### Algorithm Tuning

```cpp
const int nRUN = 3000000;   // Max iterations
int nIt = 5;                // Number of runs
const double nhp = 0.125;   // Neighborhood removal percentage
const int des = 10;         // Diversification parameter
```

## Project Structure

```
FSMS-static/
├── CMakeLists.txt          # Build configuration
├── README.md               # This file
├── LICENSE                 # Project license
├── .vscode/                # VS Code configuration
│   ├── c_cpp_properties.json
│   ├── launch.json
│   ├── settings.json
│   └── tasks.json
├── src/
│   └── main.cpp            # Main solver implementation
├── Data/
│   └── input/              # Input data files
└── build/                  # Build artifacts (generated)
```

## Algorithm Overview

### 1. Preprocessing
- Compute Manhattan distances between all entities
- Sort stops by proximity for each passenger
- Build best route skeleton (greedy insertion)

### 2. Initial Solution Construction
- Sequentially assign buses to serve passenger requests
- Use `bestStop` and `bestStop2` heuristics to:
  - Find feasible stops within walking distance
  - Insert stops into routes maintaining mandatory order
  - Adjust timetables to respect frequency and time window constraints

### 3. Large Neighborhood Search (LNS)
- **Destroy:** Remove ~12.5% of passenger assignments
- **Repair:** Reinsert using adaptive heuristics
- **Accept/Reject:** Based on solution quality
- **Iterate:** Until stopping criteria (runtime, iterations, no improvement)

### 4. Adaptive Parameters
Randomized per bus/trip:
- `pm1`, `pm2`, `pm3`: Time slack multipliers
- `fpm`: Frequency penalty multiplier
- `xt`: Headway constraint (60-100% of base)
- `C`: Bus capacity (25-100% of base)

## Development

### Debugging

Run with AddressSanitizer (Debug build):

```bash
./build/FSMS
```

ASan will report memory errors immediately if detected.

### VS Code Integration

The project includes IntelliSense configuration:
- Open folder in VS Code
- C/C++ extension reads `compile_commands.json` automatically
- Debugging configured in `.vscode/launch.json`

Press **F5** to build and debug.

### Running Tests

Currently, no automated test suite. To validate:

1. Run with small instances (R=10, B=3)
2. Check console for constraint violations
3. Verify output files for consistency

## Performance

**Typical runtime** (M1 MacBook Pro, 12 threads):
- 48 passengers, 12 buses: ~2-5 minutes per iteration
- 100 passengers, 20 buses: ~10-20 minutes per iteration

**Memory usage:** ~50-200 MB depending on problem size.

## Known Issues

- Input file paths are relative to working directory; run from project root
- OpenMP detection may fail on older macOS/Clang; build still works without parallelization
- Large instances (R > 200) may require tuning iteration limits

## Contributing

Contributions welcome! Please:

1. Fork the repository
2. Create a feature branch
3. Make changes with clear commit messages
4. Test with Debug build (ASan enabled)
5. Submit a pull request
