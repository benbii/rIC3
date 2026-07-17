cmake_minimum_required(VERSION 3.10)
project(for-rIC3 LANGUAGES C CXX)
set(CMAKE_C_FLAGS_RELEASE "-O3")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

set(S ../../deps/cadical/src/)
add_library(satif-cadical
  ${S}analyze.cpp ${S}arena.cpp ${S}assume.cpp ${S}averages.cpp
  ${S}backbone.cpp ${S}backtrack.cpp ${S}backward.cpp ${S}bins.cpp ${S}block.cpp
  ${S}ccadical.cpp ${S}checker.cpp ${S}clause.cpp ${S}collect.cpp
  ${S}compact.cpp ${S}condition.cpp ${S}config.cpp ${S}congruence.cpp ${S}constrain.cpp
  ${S}contract.cpp ${S}cover.cpp ${S}decide.cpp ${S}decompose.cpp
  ${S}deduplicate.cpp ${S}definition.cpp ${S}drattracer.cpp ${S}elim.cpp
  ${S}elimfast.cpp ${S}ema.cpp ${S}extend.cpp ${S}external.cpp
  ${S}external_propagate.cpp ${S}factor.cpp
  ${S}flags.cpp ${S}flip.cpp ${S}format.cpp ${S}frattracer.cpp ${S}gates.cpp
  ${S}idruptracer.cpp ${S}instantiate.cpp ${S}internal.cpp ${S}ipasir.cpp
  ${S}lidruptracer.cpp ${S}limit.cpp ${S}logging.cpp ${S}lookahead.cpp
  ${S}lratchecker.cpp ${S}lrattracer.cpp ${S}lucky.cpp
  ${S}message.cpp ${S}minimize.cpp ${S}occs.cpp ${S}options.cpp ${S}parse.cpp
  ${S}phases.cpp ${S}probe.cpp ${S}profile.cpp ${S}proof.cpp ${S}propagate.cpp
  ${S}queue.cpp ${S}random.cpp ${S}reap.cpp ${S}reduce.cpp ${S}rephase.cpp
  ${S}report.cpp ${S}resources.cpp ${S}restart.cpp ${S}restore.cpp
  ${S}score.cpp ${S}shrink.cpp ${S}solution.cpp ${S}solver.cpp
  ${S}stable.cpp ${S}stats.cpp ${S}subsume.cpp ${S}sweep.cpp ${S}ternary.cpp
  ${S}tier.cpp ${S}transred.cpp ${S}unstable.cpp ${S}util.cpp ${S}var.cpp
  ${S}veripbtracer.cpp ${S}vivify.cpp ${S}walk.cpp ${S}walk_full_occs.cpp
  ${S}warmup.cpp ${S}watch.cpp
  ${S}kitten.c
  bindings/binding.cpp
  win-port/file.cpp win-port/terminal.cpp
)

target_compile_definitions(satif-cadical PRIVATE QUIET NDEBUG)

# CaDiCaL 3 embeds a newer, ABI-incompatible copy of Kissat's Kitten
# subsolver.  Namespace every externally visible symbol from that copy so it
# can coexist with the copy embedded in the separately linked Kissat library.
set(CADICAL_KITTEN_SYMBOLS
  citten_clause_with_id
  citten_clause_with_id_and_equivalence
  citten_clause_with_id_and_exception
  completely_backtrack_to_root_level
  kitten_add_prime_implicant
  kitten_assume
  kitten_assume_signed
  kitten_binary
  kitten_clause
  kitten_clause_with_id_and_exception
  kitten_clear
  kitten_compute_clausal_core
  kitten_compute_prime_implicant
  kitten_current_ticks
  kitten_failed
  kitten_fixed
  kitten_fixed_signed
  kitten_flip_and_implicant_for_signed_literal
  kitten_flip_literal
  kitten_flip_phases
  kitten_flip_signed_literal
  kitten_init
  kitten_no_terminator
  kitten_no_ticks_limit
  kitten_randomize_phases
  kitten_release
  kitten_set_logging
  kitten_set_terminator
  kitten_set_ticks_limit
  kitten_shrink_to_clausal_core
  kitten_shuffle_clauses
  kitten_signed_value
  kitten_solve
  kitten_status
  kitten_trace_core
  kitten_track_antecedents
  kitten_traverse_core_clauses
  kitten_traverse_core_clauses_with_id
  kitten_traverse_core_ids
  kitten_unit
  kitten_value
  new_learned_klause
)
foreach(SYMBOL IN LISTS CADICAL_KITTEN_SYMBOLS)
  target_compile_definitions(satif-cadical PRIVATE
    "${SYMBOL}=cadical_${SYMBOL}")
endforeach()
if(WIN32)
  target_compile_definitions(satif-cadical PRIVATE
    getc_unlocked=getc putc_unlocked=putc)
endif()
target_include_directories(satif-cadical PRIVATE ${S})
install(TARGETS satif-cadical ARCHIVE DESTINATION lib LIBRARY DESTINATION lib)
