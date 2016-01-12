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
aut.prop_inherently_weak(True)
aut = spot.dtwa_complement(aut)
aut1 = spot.scc_filter_states(aut)
assert(aut1.to_str('hoa') == """HOA: v1
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

assert(aut.scc_filter_states().to_str() == aut1.to_str())
assert(aut1.get_name() == None)
aut1.set_name("test me")
assert(aut1.get_name() == "test me")
# The method is the same as the function

a = spot.translate('true', 'low', 'any')
assert(a.prop_deterministic().is_maybe())
assert(a.prop_unambiguous().is_maybe())
assert(a.is_deterministic() == True)
assert(a.is_unambiguous() == True)
