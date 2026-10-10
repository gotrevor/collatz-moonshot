from fractions import Fraction as F
from arc_carry_compatibility import forced_parity_zones
import json
from pathlib import Path
from arc_carry_compatibility import pieces_from_witness


def test_forced_opposites_and_an_alternative_move():
    # At k=3 the siblings 0 and 4 share starts (1/4,3/4).  Word 0 has floor 0;
    # word 4 has floor 1.  Adding floor 2 at word 4 cancels the obstruction
    # on (1/2,3/4), so only (1/4,1/2) remains.
    pieces = [(0, 0, F(0), F(1)), (4, 1, F(1, 4), F(3, 4)),
              (4, 2, F(1, 2), F(3, 4))]
    assert forced_parity_zones(3, pieces) == [dict(words=[0, 4],
        interval=['1/4', '1/2'], sample='3/8', floors=[[0], [1]])]


def test_touching_endpoints_are_not_an_open_conflict():
    assert forced_parity_zones(3, [(0, 0, F(0), F(1, 2)),
                                  (4, 1, F(1, 2), F(1))]) == []


def test_same_parity_is_not_an_obstruction():
    assert forced_parity_zones(3, [(0, 0, F(0), F(1)),
                                  (4, 2, F(0), F(1))]) == []


def test_exported_delay_witness_has_no_open_sibling_conflict():
    source = Path(__file__).with_name('witness_delay_b10_l31_k6.json')
    witness = json.loads(source.read_text())
    assert witness['k'] == 6 and witness['s'] == '1/10' and witness['l'] == '31/100'
    pieces = pieces_from_witness(witness)
    assert len(pieces) == 212
    assert forced_parity_zones(6, pieces) == []
    intervals = [tuple(F(x) for x in row['interval']) for row in witness['rows'] if row['word'] == 0]
    assert (F(0), F(473, 1024)) in intervals
    assert (F(2299, 4096), F(2839, 4096)) in intervals
    # These interior starts force floors 0 and 1 from window fit alone.
    assert F(3, 2) * (F(1, 10) + F(31, 300)) < 1
    assert 1 < F(3, 2) * F(17, 25)
    assert F(3, 2) * (F(17, 25) + F(31, 300)) < 2
