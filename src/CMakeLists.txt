cmake_minimum_required(VERSION 2.6)

# Create the HQSpre library
add_library(hqspre STATIC
              aux.hpp
              bool_vector.hpp
              bool_vector.ipp
              bool_vector.cpp
              clause.hpp
              clause.ipp
              clause.cpp
              formula.hpp
              formula.ipp
              formula.cpp
              formula_blocked_et_al.cpp
              formula_blocked_et_al.ipp
              formula_debug.cpp
              formula_dep_elim.cpp
              formula_dep_schemes.cpp
              formula_equiv_contra.cpp
              formula_experimental.cpp
              formula_gate_interface.cpp
              formula_gates.cpp
              formula_inout.cpp
              formula_resolution.cpp
              formula_sat.cpp
              formula_substitute.cpp
              formula_subsumption.cpp
              formula_unit_pure.cpp
              formula_univ_expand.cpp
              formula_univ_red.cpp
              literal.hpp
              prefix.hpp
              prefix.ipp
              prefix.cpp
              process_limits.hpp
              sat_solver.hpp
              settings.hpp
              settings.cpp
              timer.hpp
              timer.cpp
              varheap.hpp
           )
target_link_libraries(hqspre antom)


# Create the HQSpre binary
add_executable(preprocess main.cpp)

target_link_libraries(preprocess hqspre)
target_link_libraries(preprocess antom)
target_link_libraries(preprocess ${Boost_LIBRARIES} rt ${ZLIB_LIBRARIES})

if (SAT_SOLVER STREQUAL "Picosat")
    target_link_libraries(preprocess picosat)
elseif (SAT_SOLVER STREQUAL "Lingeling")
    target_link_libraries(preprocess lgl)
endif()


install(TARGETS preprocess hqspre
        RUNTIME DESTINATION ${CMAKE_BINARY_DIR}/bin
        LIBRARY DESTINATION ${CMAKE_BINARY_DIR}/bin
        ARCHIVE DESTINATION ${CMAKE_BINARY_DIR}/bin
       )
