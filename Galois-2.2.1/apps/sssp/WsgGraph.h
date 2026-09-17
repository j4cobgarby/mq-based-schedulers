#ifndef APPS_SSSP_WSGGRAPH_H
#define APPS_SSSP_WSGGRAPH_H

// Reads the GAP Benchmark Suite serialized weighted graph format (.wsg), so
// that this driver consumes the very same graph file as the other
// implementations in the relax-experiments harness. Node numbering is then
// identical by construction, which is what makes a shared .sources file valid.
//
// Layout, as written by gapbs / wasp's include/writer.h:
//
//   bool    directed
//   int64   num_edges                 (directed edge count)
//   int64   num_nodes
//   int64   offsets[num_nodes + 1]    out-edge CSR offsets
//   struct { int32 dst; W weight; }   [num_edges]
//   if directed:
//     int64 in_offsets[num_nodes + 1]
//     struct { int32 src; W weight; } [num_edges]   (unused by SSSP)
//
// The file is mapped rather than read into a buffer: these graphs reach
// billions of edges, and the edge section is consumed once, in order.

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#include <cstdint>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>

#include "Galois/Graph/FileGraph.h"
#include "Galois/Graph/Util.h"

namespace wsg {

//! Mapped read-only view of a file, unmapped on destruction.
class MappedFile {
public:
  explicit MappedFile(const std::string& filename) {
    fd_ = open(filename.c_str(), O_RDONLY);
    if (fd_ == -1) {
      std::cerr << "Could not open graph " << filename << "\n";
      abort();
    }
    // lseek rather than fstat: <sys/stat.h> would drag `struct stat` into the
    // including translation unit, and at least one driver defines its own.
    off_t end = lseek(fd_, 0, SEEK_END);
    if (end == -1) {
      std::cerr << "Could not size graph " << filename << "\n";
      abort();
    }
    length_ = static_cast<size_t>(end);
    data_ = static_cast<const char*>(mmap(nullptr, length_, PROT_READ, MAP_PRIVATE, fd_, 0));
    if (data_ == MAP_FAILED) {
      std::cerr << "Could not map graph " << filename << "\n";
      abort();
    }
  }

  ~MappedFile() {
    if (data_ != MAP_FAILED)
      munmap(const_cast<char*>(data_), length_);
    if (fd_ != -1)
      close(fd_);
  }

  MappedFile(const MappedFile&) = delete;
  MappedFile& operator=(const MappedFile&) = delete;

  const char* data() const { return data_; }
  size_t size() const { return length_; }

private:
  int fd_ = -1;
  size_t length_ = 0;
  const char* data_ = static_cast<const char*>(MAP_FAILED);
};

//! One out-edge as stored in the file. WeightTy must match the type the graph
//! was written with, which is why the binaries are built per weight type.
template <typename WeightTy>
struct WsgEdge {
  int32_t dst;
  WeightTy weight;
};

} // namespace wsg

//! Builds `graph` from the .wsg file at `filename`. EdgeTy is the edge data
//! type of the target graph; WeightTy is the type stored in the file. They are
//! usually the same, and differ only when the graph stores a narrower type
//! than the algorithm computes in.
template <typename Graph, typename EdgeTy, typename WeightTy = EdgeTy>
void readWsgGraph(Graph& graph, const std::string& filename) {
  using Edge = wsg::WsgEdge<WeightTy>;

  wsg::MappedFile file(filename);
  const char* p = file.data();

  bool directed;
  std::memcpy(&directed, p, sizeof(bool));
  p += sizeof(bool);

  int64_t numEdges, numNodes;
  std::memcpy(&numEdges, p, sizeof(int64_t));
  p += sizeof(int64_t);
  std::memcpy(&numNodes, p, sizeof(int64_t));
  p += sizeof(int64_t);

  if (numNodes < 0 || numEdges < 0) {
    std::cerr << "Corrupt .wsg header in " << filename << "\n";
    abort();
  }

  const int64_t* offsets = reinterpret_cast<const int64_t*>(p);
  p += static_cast<size_t>(numNodes + 1) * sizeof(int64_t);
  const Edge* edges = reinterpret_cast<const Edge*>(p);

  // The whole file size is derived from the header and required to match
  // exactly. A weaker "does the out-edge section fit" check is not enough: a
  // directed graph carries a second CSR of the same size, so a binary reading
  // with a too-wide weight type still fits inside the file and then silently
  // misparses every edge.
  size_t csrBytes = static_cast<size_t>(numNodes + 1) * sizeof(int64_t) +
                    static_cast<size_t>(numEdges) * sizeof(Edge);
  size_t expected = sizeof(bool) + 2 * sizeof(int64_t) + (directed ? 2 * csrBytes : csrBytes);
  if (file.size() != expected) {
    std::cerr << "Graph " << filename << " is " << file.size() << " bytes but its header "
              << "implies " << expected << " (" << numNodes << " nodes, " << numEdges
              << " edges, " << sizeof(Edge) << "-byte edges). This binary expects a "
              << sizeof(WeightTy) << "-byte weight type; the file was probably written "
              << "with a different one.\n";
    abort();
  }

  std::cout << "Read " << numNodes << " nodes, " << numEdges << " edges from "
            << filename << (directed ? " (directed)" : " (undirected)") << "\n";

  // Galois wants per-node end offsets, length numNodes; GAP stores numNodes + 1
  // offsets starting at zero.
  std::vector<uint64_t> outIdx(static_cast<size_t>(numNodes));
  for (int64_t i = 0; i < numNodes; ++i)
    outIdx[static_cast<size_t>(i)] = static_cast<uint64_t>(offsets[i + 1]);

  std::vector<uint32_t> outs(static_cast<size_t>(numEdges));
  for (int64_t e = 0; e < numEdges; ++e)
    outs[static_cast<size_t>(e)] = static_cast<uint32_t>(edges[e].dst);

  Galois::Graph::FileGraph fileGraph;
  EdgeTy* edgeData = fileGraph.structureFromArrays<EdgeTy>(
      outIdx.data(), static_cast<uint64_t>(numNodes),
      outs.data(), static_cast<uint64_t>(numEdges));

  for (int64_t e = 0; e < numEdges; ++e)
    edgeData[e] = static_cast<EdgeTy>(edges[e].weight);

  std::vector<uint32_t>().swap(outs);
  std::vector<uint64_t>().swap(outIdx);

  Galois::Graph::readGraph(graph, fileGraph);
}

//! True when the harness handed us a GAP serialized graph rather than a .gr.
inline bool isWsgFilename(const std::string& filename) {
  return filename.size() >= 4 && filename.compare(filename.size() - 4, 4, ".wsg") == 0;
}

#endif
