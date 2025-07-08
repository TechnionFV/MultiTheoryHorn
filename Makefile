# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
ifndef Z3_ROOT
$(error Z3_ROOT is undefined. Please export Z3_ROOT to point at your Z3 install root)
endif

INCLUDES 	:=  -I$(Z3_ROOT)/src/api/c++ \
				-I$(Z3_ROOT)/src \
				-I$(Z3_ROOT)/src/api \
				-I$(CURDIR)/src

LIBS      	:= -L$(Z3_ROOT)/build -lz3

CXX       	:= g++
CXXFLAGS  	:= -std=c++17 -g $(INCLUDES)

BUILD_DIR 	:= build
BIN_DIR  	:= bins

#  1) All .cpp in src/ → build/*.o
SRC_CPP 	:= $(wildcard src/*.cpp)
SRC_OBJS	:= $(patsubst src/%.cpp,$(BUILD_DIR)/%.o,$(SRC_CPP))

# 2) All .cpp in benchmarks/ → bins/
BENCH_CPP 	:= $(wildcard benchmarks/*.cpp)
BENCH_BIN   := $(patsubst benchmarks/%.cpp,$(BIN_DIR)/%,$(BENCH_CPP))

.PHONY: all
all: $(SRC_OBJS) $(BENCH_BIN)

# Compile core objects
$(BUILD_DIR)/%.o: src/%.cpp
	@mkdir -p $(BUILD_DIR)
	$(CXX) $(CXXFLAGS) -c $< -o $@

# Link each benchmark into its own binary
$(BIN_DIR)/%: benchmarks/%.cpp $(SRC_OBJS)
	@mkdir -p $(BIN_DIR)
	$(CXX) $(CXXFLAGS) $< $(SRC_OBJS) -o $@ $(LIBS)

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR) $(BIN_DIR)

