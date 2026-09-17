set(CMAKE_CXX_STANDARD 17)
app(sssp-all SSSPall.cpp)
app(sssp SSSP.cpp)
target_link_libraries(sssp libatomic.so)

# The relax-experiments harness addresses binaries as <name>-<weight type>,
# matching the weight type the graph file itself was written with.
app(sssp-int32 SSSP.cpp)
target_link_libraries(sssp-int32 libatomic.so)

app(sssp-float SSSP.cpp)
target_link_libraries(sssp-float libatomic.so)
target_compile_definitions(sssp-float PRIVATE USE_FLOAT)
