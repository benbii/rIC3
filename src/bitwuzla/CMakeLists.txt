cmake_minimum_required(VERSION 3.10)
project(for-rIC3 LANGUAGES C CXX)
set(CMAKE_C_STANDARD 17)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_C_FLAGS_RELEASE "-O3")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

set(R ${CMAKE_CURRENT_SOURCE_DIR}/../../deps/bitwuzla)
set(S ${R}/src)
set(is_debug_build false)
if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(is_debug_build true)
endif()
set(git_id "")
set(version "0.8.2-dev")
set(is_dev_version true)
set(is_git_version false)
set(os "${CMAKE_SYSTEM_NAME}")
set(cc "${CMAKE_C_COMPILER_ID} ${CMAKE_C_COMPILER_VERSION}")
set(cxx "${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")
set(license "ric3 internal. all gpl")
configure_file(${S}/config.h.in ${CMAKE_CURRENT_BINARY_DIR}/config.h @ONLY)

add_library(smtif-bitwuzla STATIC
  ${S}/util/hash.cpp
  ${S}/util/logger.cpp
  ${S}/util/resources.cpp
  ${S}/util/printer.cpp
  ${S}/util/statistics.cpp
  ${S}/util/util.cpp
  ${S}/util/integer.cpp
  ${S}/util/gmp_utils.cpp
  ${S}/lib/bv/bitvector.cpp
  ${S}/lib/bv/bounds/bitvector_bounds.cpp
  ${S}/lib/bv/domain/bitvector_domain.cpp
  ${S}/lib/bv/domain/wheel_factorizer.cpp
  ${S}/lib/bitblast/aig/aig_cnf.cpp
  ${S}/lib/bitblast/aig/aig_manager.cpp
  ${S}/lib/bitblast/aig/aig_node.cpp
  ${S}/lib/bitblast/aig/aig_printer.cpp
  ${S}/lib/ls/ls.cpp
  ${S}/lib/ls/ls_bv.cpp
  ${S}/lib/ls/bv/bitvector_node.cpp
  ${S}/lib/ls/node/node.cpp
  ${S}/lib/rng/rng.cpp

  ${S}/api/c/bitwuzla.cpp
  ${S}/api/c/bitwuzla_structs.cpp
  ${S}/api/checks.cpp
  ${S}/api/cpp/bitwuzla.cpp
  ${S}/backtrack/assertion_stack.cpp
  ${S}/backtrack/backtrackable.cpp
  ${S}/check/check_model.cpp
  ${S}/check/check_unsat_core.cpp
  ${S}/check/check_term.cpp
  ${S}/env.cpp
  ${S}/node/kind_info.cpp
  ${S}/node/node.cpp
  ${S}/node/node_data.cpp
  ${S}/node/node_kind.cpp
  ${S}/node/node_manager.cpp
  ${S}/node/node_unique_table.cpp
  ${S}/node/node_utils.cpp
  ${S}/option/option.cpp
  ${S}/preprocess/assertion_tracker.cpp
  ${S}/preprocess/assertion_vector.cpp
  ${S}/preprocess/pass/contradicting_ands.cpp
  ${S}/preprocess/pass/elim_extract.cpp
  ${S}/preprocess/pass/elim_lambda.cpp
  ${S}/preprocess/pass/elim_udiv.cpp
  ${S}/preprocess/pass/elim_uninterpreted.cpp
  ${S}/preprocess/pass/embedded_constraints.cpp
  ${S}/preprocess/pass/flatten_and.cpp
  ${S}/preprocess/pass/normalize.cpp
  ${S}/preprocess/pass/rewrite.cpp
  ${S}/preprocess/pass/skeleton_preproc.cpp
  ${S}/preprocess/pass/variable_substitution.cpp
  ${S}/preprocess/preprocessing_pass.cpp
  ${S}/preprocess/preprocessor.cpp
  ${S}/printer/btor2_printer.cpp
  ${S}/printer/smt2_printer.cpp
  ${S}/parser/smt2/lexer.cpp
  ${S}/rewrite/evaluator.cpp
  ${S}/rewrite/rewrite_utils.cpp
  ${S}/rewrite/rewriter.cpp
  ${S}/rewrite/rewrites_array.cpp
  ${S}/rewrite/rewrites_bool.cpp
  ${S}/rewrite/rewrites_bv.cpp
  ${S}/rewrite/rewrites_bv_norm.cpp
  ${S}/rewrite/rewrites_core.cpp
  ${S}/rewrite/rewrites_fp.cpp
  ${S}/resource_terminator.cpp
  ${S}/sat/cadical.cpp
  ${S}/sat/sat_solver_factory.cpp
  ${S}/solver/array/array_solver.cpp
  ${S}/solver/abstract/abstraction_lemmas.cpp
  ${S}/solver/abstract/abstraction_module.cpp
  ${S}/solver/bv/bv_bitblast_solver.cpp
  ${S}/solver/bv/bv_prop_solver.cpp
  ${S}/solver/bv/bv_solver.cpp
  ${S}/solver/bv/aig_bitblaster.cpp
  ${S}/solver/fp/floating_point.cpp
  ${S}/solver/fp/fp_solver.cpp
  ${S}/solver/fp/rounding_mode.cpp
  ${S}/solver/fp/symfpu_nm.cpp
  ${S}/solver/fp/symfpu_floating_point_typeinfo.cpp
  ${S}/solver/fp/symfpu_wrapper.cpp
  ${S}/solver/fp/word_blaster.cpp
  ${S}/solver/fun/fun_solver.cpp
  ${S}/solver/quant/quant_solver.cpp
  ${S}/solver/result.cpp
  ${S}/solver/solver.cpp
  ${S}/solver/solver_engine.cpp
  ${S}/solver/solver_state.cpp
  ${S}/solving_context.cpp
  ${S}/type/type.cpp
  ${S}/type/type_data.cpp
  ${S}/type/type_manager.cpp
)

target_compile_definitions(smtif-bitwuzla PRIVATE MPFR_USE_C99_FEATURE=1 NDEBUG)
if(UNIX AND NOT APPLE)
  target_compile_definitions(smtif-bitwuzla PRIVATE HAVE_RUSAGE)
endif()
target_include_directories(smtif-bitwuzla PRIVATE
  ${CMAKE_CURRENT_BINARY_DIR}
  ${R}/include ${S} ${S}/lib
  ${CMAKE_CURRENT_SOURCE_DIR}/gmp-6.3.0
  ${CMAKE_CURRENT_SOURCE_DIR}/mpfr-4.2.2/src
  ${CMAKE_CURRENT_SOURCE_DIR}/../../deps/cadical/src
  ${CMAKE_CURRENT_SOURCE_DIR}/../../deps #symfpu
)
