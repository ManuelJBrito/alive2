add_llvm_library(tv MODULE PARTIAL_SOURCES_INTENDED tv.cpp)

configure_file(
  ${PROJECT_SOURCE_DIR}/scripts/alivecc.in
  ${PROJECT_BINARY_DIR}/alivecc
  @ONLY
)
configure_file(
  ${PROJECT_SOURCE_DIR}/scripts/alivecc.in
  ${PROJECT_BINARY_DIR}/alive++
  @ONLY
)
configure_file(
  ${PROJECT_SOURCE_DIR}/scripts/benchmark-clang-tv.in
  ${PROJECT_BINARY_DIR}/benchmark-clang-tv
  @ONLY
)
configure_file(
  ${PROJECT_SOURCE_DIR}/scripts/benchmark-llvm-test-suite.in
  ${PROJECT_BINARY_DIR}/benchmark-llvm-test-suite
  @ONLY
)

target_link_libraries(tv PRIVATE ${ALIVE_LIBS_LLVM} ${Z3_LIBRARIES} ${HIREDIS_LIBRARIES})
target_compile_options(tv PRIVATE -fexceptions)

add_llvm_library(alive-red-pass MODULE PARTIAL_SOURCES_INTENDED alive-red-pass.cpp)
target_link_libraries(alive-red-pass PRIVATE ${ALIVE_LIBS_LLVM} ${Z3_LIBRARIES} ${HIREDIS_LIBRARIES})
target_compile_options(alive-red-pass PRIVATE -fexceptions)

# Detect AfterGVN extension point (custom addition to BenchGVN LLVM tree)
foreach(_inc_dir ${LLVM_INCLUDE_DIRS})
  if(EXISTS "${_inc_dir}/llvm/Passes/PassBuilder.h")
    file(READ "${_inc_dir}/llvm/Passes/PassBuilder.h" _pb_header)
    if(_pb_header MATCHES "registerAfterGVNEPCallback")
      target_compile_definitions(alive-red-pass PRIVATE ALIVE_RED_HAS_AFTER_GVN_EP)
    endif()
    break()
  endif()
endforeach()

if(APPLE)
    set_target_properties(tv PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup"
    )
    set_target_properties(alive-red-pass PROPERTIES
        LINK_FLAGS "-undefined dynamic_lookup"
    )
endif(APPLE)
