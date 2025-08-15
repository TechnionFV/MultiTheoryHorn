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

BUILD_DIR 		:= build
SRC_BIN_DIR 	:= $(BUILD_DIR)/src
BIN_DIR  		:= $(BUILD_DIR)/bin
TEST_BIN_DIR	:= $(BUILD_DIR)/tests

#  1) All .cpp in src/ → build/src
SRC_CPP 	:= $(wildcard src/*.cpp)
SRC_OBJS	:= $(patsubst src/%.cpp,$(SRC_BIN_DIR)/%.o,$(SRC_CPP))

# 2) All .cpp in benchmarks/ → build/bin
BENCH_CPP 	:= $(wildcard benchmarks/*.cpp)
BENCH_BIN   := $(patsubst benchmarks/%.cpp,$(BIN_DIR)/%,$(BENCH_CPP))

# 3) All .cpp in tests/ → build/tests
TEST_CPP 	:= $(wildcard tests/*.cpp)
TEST_BIN   := $(patsubst tests/%.cpp,$(TEST_BIN_DIR)/%,$(TEST_CPP))

all: $(SRC_OBJS) $(BENCH_BIN) $(Z3_SYMLINK) $(TEST_BIN)

# Compile core objects
$(SRC_BIN_DIR)/%.o: src/%.cpp
	@mkdir -p $(SRC_BIN_DIR)
	$(CXX) $(CXXFLAGS) -c $< -o $@

# Link each benchmark into its own binary
$(BIN_DIR)/%: benchmarks/%.cpp $(SRC_OBJS)
	@mkdir -p $(BIN_DIR)
	$(CXX) $(CXXFLAGS) $< $(SRC_OBJS) -o $@ $(LIBS)

# Link each test into its own binary
$(TEST_BIN_DIR)/%: tests/%.cpp $(SRC_OBJS)
	@mkdir -p $(TEST_BIN_DIR)
	$(CXX) $(CXXFLAGS) $< $(SRC_OBJS) -o $@ $(LIBS)

Z3_SYMLINK := z3
# Create a directory z3 which is symbolically linked to the Z3_ROOT
.PHONY: $(Z3_SYMLINK)
z3:
	@rm -rf $(Z3_SYMLINK)
	@ln -s $(Z3_ROOT) $(Z3_SYMLINK)

.PHONY: all
all: $(SRC_OBJS) $(BENCH_BIN) $(Z3_SYMLINK) $(TEST_BIN)

.PHONY: clean
clean:
	rm -rf $(BUILD_DIR) $(Z3_SYMLINK)

