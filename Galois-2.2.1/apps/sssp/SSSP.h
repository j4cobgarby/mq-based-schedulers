/** Single source shortest paths -*- C++ -*-
 * @file
 * @section License
 *
 * Galois, a framework to exploit amorphous data-parallelism in irregular
 * programs.
 *
 * Copyright (C) 2013, The University of Texas at Austin. All rights reserved.
 * UNIVERSITY EXPRESSLY DISCLAIMS ANY AND ALL WARRANTIES CONCERNING THIS
 * SOFTWARE AND DOCUMENTATION, INCLUDING ANY WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR ANY PARTICULAR PURPOSE, NON-INFRINGEMENT AND WARRANTIES OF
 * PERFORMANCE, AND ANY WARRANTY THAT MIGHT OTHERWISE ARISE FROM COURSE OF
 * DEALING OR USAGE OF TRADE.  NO WARRANTY IS EITHER EXPRESS OR IMPLIED WITH
 * RESPECT TO THE USE OF THE SOFTWARE OR DOCUMENTATION. Under no circumstances
 * shall University be liable for incidental, special, indirect, direct or
 * consequential damages or loss of profits, interruption of business, or
 * related expenses which may arise from use of Software or Documentation,
 * including but not limited to those resulting from defects in Software and/or
 * Documentation, or loss or inaccuracy of data of any kind.
 *
 * @section Description
 *
 * Single source shortest paths.
 *
 * @author Andrew Lenharth <andrewl@lenharth.org>
 */
#ifndef APPS_SSSP_SSSP_H
#define APPS_SSSP_SSSP_H

#include "llvm/Support/CommandLine.h"

#include <limits>
#include <string>
#include <sstream>
#include <stdint.h>
#include <cstring>

// Weight type as stored in the graph file, and the type distances are computed
// in. Built both ways so the harness can address <binary>-int32 / <binary>-float,
// matching how the graph files themselves are typed.
#ifdef USE_FLOAT
typedef float wsg_weight_type;
typedef float Dist;
static const Dist DIST_INFINITY = std::numeric_limits<Dist>::max() / 2 - 1;
#else
typedef int32_t wsg_weight_type;
typedef unsigned long Dist;
static const Dist DIST_INFINITY = std::numeric_limits<Dist>::max() - 1;
#endif

// The value actually stored in a node. The integer build packs a work counter
// (see trackWork in SSSP.cpp) into the high 32 bits of the 64-bit distance
// word, so a distance is read back by narrowing to the low half; the float
// build stores the distance on its own and needs no unpacking. Casting through
// DistVal is what the original `(unsigned int)` casts were doing.
#ifdef USE_FLOAT
typedef Dist DistVal;
#else
typedef unsigned int DistVal;
#endif

// Compare-and-swap on a distance. The integer builds swap the value directly.
// For float we swap the bit pattern instead, since the atomic builtins reject
// floating-point operands; SSSP distances are non-negative, and IEEE-754 orders
// non-negative floats identically to their bit patterns, so this is exact.
inline bool casDist(Dist* addr, Dist expected, Dist desired) {
#ifdef USE_FLOAT
  static_assert(sizeof(Dist) == sizeof(uint32_t), "float Dist is expected to be 32-bit");
  uint32_t e, d;
  std::memcpy(&e, &expected, sizeof(e));
  std::memcpy(&d, &desired, sizeof(d));
  return __sync_bool_compare_and_swap(reinterpret_cast<uint32_t*>(addr), e, d);
#else
  return __sync_bool_compare_and_swap(addr, expected, desired);
#endif
}

template<typename GrNode>
struct UpdateRequestCommon {
  GrNode n;
  Dist w;

  UpdateRequestCommon(const GrNode& N, Dist W): n(N), w(W) {}

  UpdateRequestCommon(): n(), w(0) {}

  Dist prior() const {
    return w;
  }

  bool operator>(const UpdateRequestCommon& rhs) const {
    if (w > rhs.w) return true;
    if (w < rhs.w) return false;
    return n > rhs.n;
  }

  bool operator<(const UpdateRequestCommon& rhs) const {
    if (w < rhs.w) return true;
    if (w > rhs.w) return false;
    return n < rhs.n;
  }

  bool operator!=(const UpdateRequestCommon& other) const {
    if (w != other.w) return true;
    return n != other.n;
  }

  bool operator==(const UpdateRequestCommon& other) const {
    return w == other.w && n == other.n;
  }

  uintptr_t getID() const {
    return reinterpret_cast<uintptr_t>(n);
  }

  unsigned int operator() () const {
    return w;
  }
};

struct SNode {
  Dist dist;
};

template<typename Graph>
void readInOutGraph(Graph& graph);

extern llvm::cl::opt<unsigned int> memoryLimit;


#endif
