cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

project(tip)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." ON)
option(USE_SORELEASE   "Use SORELEASE in shared library filename." ON)

#--------------------------------------------------------------------------------------------------
# Library version:

set(TIP_SOMAJOR   1)
set(TIP_SOMINOR   0)
set(TIP_SORELEASE 0)

# Compute VERSION and SOVERSION:
if(USE_SORELEASE)
  set(TIP_VERSION ${TIP_SOMAJOR}.${TIP_SOMINOR}.${TIP_SORELEASE})
else()
  set(TIP_VERSION ${TIP_SOMAJOR}.${TIP_SOMINOR})
endif()
set(TIP_SOVERSION ${TIP_SOMAJOR})

#--------------------------------------------------------------------------------------------------
# Dependencies:

include_directories(${minisat_SOURCE_DIR})
include_directories(${mcl_SOURCE_DIR})
include_directories(${tip_SOURCE_DIR})

#--------------------------------------------------------------------------------------------------
# Build Targets:

set(TIP_LIB_SOURCES
    tip/unroll/SimpBmc.cc
    tip/unroll/SimpBmc2.cc
    tip/unroll/BasicBmc.cc
    tip/unroll/Unroll.cc
    tip/constraints/Embed.cc
    tip/constraints/Extract.cc
    tip/induction/RelativeInduction.cc
    tip/induction/TripProofInstances.cc
    tip/liveness/EmbedFairness.cc
    tip/liveness/Liveness.cc
    tip/reductions/RemoveUnused.cc
    tip/reductions/ExtractSafety.cc
    tip/reductions/Substitute.cc
    tip/reductions/TemporalDecomposition.cc
    tip/TipCirc.cc)

add_library(tip-lib-static STATIC ${TIP_LIB_SOURCES})
add_library(tip-lib-shared SHARED ${TIP_LIB_SOURCES})

target_link_libraries(tip-lib-shared minisat-lib-shared mcl-lib-shared)
target_link_libraries(tip-lib-static minisat-lib-static mcl-lib-static)

set_target_properties(tip-lib-static PROPERTIES OUTPUT_NAME "tip")
set_target_properties(tip-lib-shared 
  PROPERTIES
    OUTPUT_NAME "tip" 
    VERSION ${TIP_VERSION}
    SOVERSION ${TIP_SOVERSION})

add_executable(tip tip/Main.cc)

#if(STATIC_BINARIES)
  target_link_libraries(tip tip-lib-static)
#else()
#  target_link_libraries(tip tip-lib-shared)
#endif()


#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS tip-lib-static tip-lib-shared tip
        RUNTIME DESTINATION bin
        LIBRARY DESTINATION lib
        ARCHIVE DESTINATION lib)

install(DIRECTORY tip tip/bmc
        DESTINATION include/tip
        FILES_MATCHING PATTERN "*.h")
