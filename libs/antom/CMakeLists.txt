cmake_minimum_required(VERSION 2.6)

# Create the Antom SAT solver library
add_library(antom STATIC antom.cpp
                      debug.cpp
                      lifting.cpp
                      maxantom.cpp
                      preprocessor.cpp)

install(TARGETS antom
        RUNTIME DESTINATION ${CMAKE_BINARY_DIR}/bin
        LIBRARY DESTINATION ${CMAKE_BINARY_DIR}/bin
        ARCHIVE DESTINATION ${CMAKE_BINARY_DIR}/bin
       )

