import spot
import spot.ltsmin
import tempfile
import shutil
import sys

spot.ltsmin.require('divine')

# the test case actually starts here
with tempfile.NamedTemporaryFile(dir='.', suffix='.dve') as fp:
    fp.write(b"""int f = 3;
process R {
  int p = 1, found = 0;
  state i, e;
  init i;
  trans
    i -> i {guard p != f; effect p = p + 1;},
    i -> e {guard p == f; effect found = 1;},
    e -> e {};
}
system async;
""")
    fp.flush()
    m = spot.ltsmin.load(fp.name)

    def modelcheck(formula, model):
        a = spot.translate(formula)
        k = m.kripke([ap.ap_name() for ap in a.ap()])
        p = spot.otf_product(k, a)
        return p.is_empty()

    assert(modelcheck('X "R.found"', m) == True)
