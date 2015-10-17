import spot

# This test used to trigger an assertion (or a segfault)
# in scc_filter_states().
aut = spot.automaton("""
HOA: v1
States: 3
Start: 1
AP: 1 "a"
Acceptance: 1 Inf(0)
--BODY--
State: 0 {0}
[t] 0
State: 1
[!0] 0
[0] 2
State: 2
[t] 2
--END--
""")
aut.prop_inherently_weak()
aut = spot.dtwa_complement(aut)
aut = spot.scc_filter_states(aut)
assert(aut.to_str('hoa') == """HOA: v1
States: 2
Start: 0
AP: 1 "a"
acc-name: co-Buchi
Acceptance: 1 Fin(0)
properties: trans-labels explicit-labels state-acc deterministic
properties: inherently-weak
--BODY--
State: 0
[0] 1
State: 1
[t] 1
--END--""")
