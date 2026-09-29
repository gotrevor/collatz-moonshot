#!/usr/bin/env -S uv run --quiet python3
"""Exact known-path profiles for the fixed inverse-five Collatz certificate."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path

import catalytic_palette
import research_lifts


INVERSE_FIVE_ODDS = [7, 7, 11, 17, 55, 65, 83]


def odd_counts(path):
    return Counter(u for u in path[:-1] if u % 2)


def sorted_counts(counts):
    return [[u, counts[u]] for u in sorted(counts) if counts[u]]


def profile(n):
    data = research_lifts.wild_five_repair(n)
    ledger = catalytic_palette.palette_ledger(n)
    actual = data['actual_path']
    smaller = data['smaller_path']
    virtual = data['virtual_prefix'] + smaller[1:]
    actual_odds = odd_counts(actual)
    virtual_odds = odd_counts(virtual)
    virtual_odds.update(INVERSE_FIVE_ODDS)
    actual_only = actual_odds - virtual_odds
    virtual_only = virtual_odds - actual_odds
    ai, si = data['meeting_steps']
    assert actual[ai:] == smaller[si:]
    mismatch = {u: actual_odds[u]-virtual_odds[u]
                for u in actual_odds.keys() | virtual_odds.keys()
                if u % 3 == 0 and actual_odds[u] != virtual_odds[u]}
    assert actual_odds[3] == virtual_odds[3] == 0
    actual_three = {u: c for u, c in actual_odds.items() if u % 3 == 0}
    virtual_three = {u: c for u, c in virtual_odds.items() if u % 3 == 0}
    assert actual_three == ({n: 1} if n % 3 == 0 else {})
    assert virtual_three == ({5*n: 1} if n % 3 == 0 else {})
    assert data['smaller_endpoint'] == 45*((n-7)//64)+5
    return {
        'n': n, 'k': (n-7)//64, 'smaller_endpoint': data['smaller_endpoint'],
        'virtual_six_step_prefix': data['virtual_prefix'],
        'actual_steps': len(actual)-1,
        'smaller_steps': len(smaller)-1,
        'meeting_value': data['meeting'],
        'meeting_steps_actual_smaller': [ai, si],
        'shared_tail_steps': len(actual)-1-ai,
        'actual_prefix_parity_to_meeting': ''.join(str(u%2) for u in actual[:ai]),
        'actual_prefix_to_meeting': actual[:ai+1],
        'smaller_prefix_to_meeting': smaller[:si+1],
        'actual_only_odd_labels': sorted_counts(actual_only),
        'virtual_only_odd_labels': sorted_counts(virtual_only),
        'common_odd_factor_count': sum((actual_odds & virtual_odds).values()),
        'forced_net_moves': ledger['forced_net_moves'],
        'r3_multiplicity_actual_virtual': [actual_odds[3], virtual_odds[3]],
        'three_divisible_label_difference': sorted_counts(mismatch),
        'has_three_divisible_label_mismatch': bool(mismatch),
    }


def fixed_offset_descent(family, j):
    if family == 'plus':
        if j < 11:
            raise ValueError('plus formula requires j>=11')
        c, length, odds, base_endpoint = 7, 11, 5, 1
    elif family == 'minus':
        if j < 8:
            raise ValueError('minus formula requires j>=8')
        c, length, odds, base_endpoint = -57, 8, 5, -53
    else:
        raise ValueError('family must be plus or minus')
    n = 2**j + c
    predicted = 3**odds * 2**(j-length) + base_endpoint
    actual = n
    bits = []
    for _ in range(length):
        bits.append(str(actual % 2))
        actual = research_lifts.step(actual)
    assert actual == predicted and 0 < actual < n
    return {'family': family, 'j': j, 'n': n, 'steps': length,
            'parity_prefix': ''.join(bits), 'endpoint': actual,
            'formula': f'243*2^({j}-{length}){base_endpoint:+d}',
            'strict_descent': actual < n}


def long_growth(j):
    """A 7 mod 64 family forced to climb for six steps plus j odd steps."""
    if j < 2:
        raise ValueError('long-growth construction requires j>=2')
    modulus = 2**j
    k = (-11 * pow(81, -1, modulus)) % modulus
    if k % 3 == 2:
        k += modulus
    n = 64*k+7
    p = 81*k+10
    assert (p+1) % modulus == 0 and n % 3 != 0
    six = [n]
    for _ in range(6):
        six.append(research_lifts.step(six[-1]))
    assert six[-1] == p and all(x > n for x in six[1:])
    x = p
    for _ in range(j):
        assert x % 2 == 1 and x > n
        x = research_lifts.step(x)
    s = (p+1)//modulus
    endpoint = 3**j*s-1
    assert x == endpoint and endpoint > n
    return {'j': j, 'k': k, 'n': n, 'initial_six': six,
            'post_six': p, 'odd_run_length': j, 's': s,
            'endpoint_after_six_plus_j': endpoint,
            'no_descent_through_six_plus_j': True}


def lower_prefix(h):
    """The fixed six-step word and ensuing odd run in the lower five-head family."""
    if h < 0:
        raise ValueError('lower-prefix requires h>=0')
    k = 144 + 255*h
    n, c, d = 9223 + 16320*h, 3689 + 6528*h, 5425 + 9600*h
    six = [64*k+7, 96*k+11, 144*k+17, 216*k+26,
           108*k+13, 162*k+20, 81*k+10]
    p = six[-1]
    assert six[0] == n and p+1 == 11675+20655*h
    assert all(x > n for x in six[1:]) and 0 < c < n and 0 < d < n
    # For p odd, the next v_2(p+1) shortcut steps are odd.  For p even,
    # this run is empty; the immediate halving is reported separately.
    run = 0
    s = p+1
    while s % 2 == 0:
        run += 1
        s //= 2
    odd_run = [3**i * 2**(run-i) * s - 1 for i in range(1, run+1)]
    endpoint = odd_run[-1] if odd_run else p
    assert endpoint > n and all(x > n for x in odd_run)
    if h % 2 == 0:
        descent_step, descent_endpoint = 7, p//2
    elif h % 4 == 1:
        descent_step, descent_endpoint = 8, (3*p+1)//4
    else:
        descent_step, descent_endpoint = None, None
    if descent_step is not None:
        assert descent_endpoint < n
    return {'h': h, 'k': k, 'n': n, 'c': c, 'd': d,
            'initial_six': six, 'post_six': p,
            'odd_run_length': run, 's': s, 'odd_run_prefix': odd_run,
            'rising_prefix_steps': 6+run,
            'endpoint_after_six_plus_odd_run': endpoint,
            'no_descent_through_six_plus_odd_run': True,
            'first_obvious_descent_step': descent_step,
            'first_obvious_descent_endpoint': descent_endpoint}


def lower_growth(j):
    """Least nonnegative h forcing at least j odd steps after the fixed six."""
    if j < 2:
        raise ValueError('lower-growth construction requires j>=2')
    modulus = 2**j
    h = (-11675 * pow(20655, -1, modulus)) % modulus
    result = lower_prefix(h)
    assert (result['post_six']+1) % modulus == 0
    assert result['odd_run_length'] >= j
    return {'requested_min_odd_run': j, 'residue_modulus': modulus,
            **result}


def lower_composite(family, t):
    """Two local Q rows; no assumption that their auxiliary labels are borrowable."""
    if t < 0:
        raise ValueError('lower-composite requires t>=0')
    if family == 'class95':
        h = 2+95*t
        x, z, b = 3349+124032*t, 785+29070*t, 661+24480*t
    elif family == 'class79':
        h = 1+79*t
        x, z, b = 3005+151680*t, 5635+284400*t, 2425+122400*t
    else:
        raise ValueError('family must be class95 or class79')
    n, c, d = 9223+16320*h, 3689+6528*h, 5425+9600*h
    m = 45*((n-7)//64)+5
    a, v = (3*n+1)//2, (15*n+1)//2
    assert all(0 < q < m for q in (c,d,x,z,b))
    assert all(q%2 and q%3 for q in (n,c,d,x,z,b,v,a))
    def pair_equal(u,w,p,q):
        return u*w*(3*p+1)*(3*q+1) == p*q*(3*u+1)*(3*w+1)
    assert pair_equal(x,z,c,b)
    assert pair_equal(5*n,c,n,d)
    assert (5*n)*x*z*(3*n+1)*(3*d+1)*(3*b+1) == (
        n*d*b*(15*n+1)*(3*x+1)*(3*z+1))
    boundary = Counter()
    for sign, q in ((1,n),(1,d),(1,b),(-1,5*n),(-1,x),(-1,z)):
        boundary[q] += sign
        boundary[(3*q+1)//2] -= sign
    central = Counter({5*n:1,n:-1})
    # Preserve negative coordinates; Counter arithmetic would drop them.
    for q, coefficient in boundary.items():
        central[q] += coefficient
    central = {q: coefficient for q, coefficient in central.items() if coefficient}
    assert max(central) == v and central[v] == 1
    assert a%64 == (43 if h%2 else 11)
    p = 11674+20655*h
    assert p%5 == 4 and v%5 == 3
    six = [64*((n-7)//64)+7, 96*((n-7)//64)+11,
           144*((n-7)//64)+17, 216*((n-7)//64)+26,
           108*((n-7)//64)+13, 162*((n-7)//64)+20, p]
    assert v > max(six)
    return {'family':family,'t':t,'h':h,'n':n,'m':m,'c':c,'d':d,
            'x':x,'z':z,'b':b,'actual_successor':a,'virtual_successor':v,
            'actual_successor_mod64':a%64,'all_auxiliaries_below_m':True,
            'virtual_successor_above_initial_six':True,
            'virtual_successor_mod5':v%5,'odd_run_mod5':p%5,
            'central_boundary_after_initial_defect':[
                [q,central[q]] for q in sorted(central)]}


def second_frontier_pairs(family, t, ceiling='m'):
    """Complete one-row scan with both auxiliaries below the chosen ceiling."""
    data = lower_composite(family,t)
    a, v, m = data['actual_successor'], data['virtual_successor'], data['m']
    assert v == 5*a-2
    limit = data['n'] if ceiling == 'n' else m
    pairs = []
    three_free_pairs = []
    for c in range(1,limit,2):
        denominator = 5*a*(3*a-1)-6*(2*a-1)*c
        if denominator <= 0:
            break
        numerator = (5*a-2)*c*(3*a+1)
        d, remainder = divmod(numerator,denominator)
        if remainder == 0 and 0 < d < limit and d%2 == 1:
            assert v*c*(3*a+1)*(3*d+1) == a*d*(3*v+1)*(3*c+1)
            pairs.append([c,d])
            if c%3 and d%3:
                three_free_pairs.append([c,d])
    return {'family':family,'t':t,'n':data['n'],'m':m,'actual_successor':a,
            'virtual_successor':v,'scope':f'positive odd c,d<{ceiling}',
            'pairs':pairs,'three_free_pairs':three_free_pairs}


def second_frontier_cubic(s, variant='hard64'):
    """A cubic scalar identity; the default CRT class has hard odd-run inputs."""
    if s < 0:
        raise ValueError('second-frontier-cubic requires s>=0')
    if variant == 'hard64':
        t, t_stride, qden, eden, shift = 16475+25172*s, 25172, 64, 58, 61
        assert t%116 == 3 and t%7 == 4 and t%31 == 14
    elif variant == 'easy32':
        t, t_stride, qden, eden, shift = 4540+5642*s, 5642, 32, 26, 29
        assert t%26 == 16 and t%7 == 4 and t%31 == 14
    else:
        raise ValueError('variant must be hard64 or easy32')
    data = lower_composite('class95',t)
    a, v, m = data['actual_successor'],data['virtual_successor'],data['m']
    assert (3*a-1)%qden == 0 and (3*a+1)%eden == 0
    assert 5*(2*a-7)%93 == 0 and (2*a-7)%21 == 0
    q1,e1 = (3*a-1)//qden,(3*a+1)//eden
    q2,e2 = 5*(2*a-7)//93,(2*a-7)//21
    labels = (q1,q2,e1,e2)
    assert all(0<u<m and u%2 == 1 and u%3 != 0 for u in labels)
    def ratio(u):
        return Fraction(2*u,3*u+1)
    common = Fraction(4*(2*a-7),3*(9*a+shift))
    assert ratio(v)*ratio(q1)*ratio(q2) == common
    assert ratio(a)*ratio(e1)*ratio(e2) == common
    w, a2 = (3*v+1)//2,(3*a+1)//2
    assert w == 16*m and w > v and a2 < w
    p_plus_one = 11675+20655*data['h']
    run, odd_part = 0, p_plus_one
    while odd_part%2 == 0:
        run += 1
        odd_part //= 2
    near_miss = {}
    if variant == 'hard64':
        assert data['h']%4 == 3 and run >= 2
        # The actual third vertex sits just below an IH-known basin vertex:
        # q1<m gives T(q1) in the basin, hence also 32*T(q1).  The factor
        # identity alone does not connect the two vertices across the gap.
        q1_successor = (3*q1+1)//2
        e1_successor = (3*e1+1)//2
        known_basin_neighbor = 32*q1_successor
        actual_third = (3*a2+1)//2
        actual_sixth = 18*q1+1
        assert a2 == 29*e1
        assert known_basin_neighbor == 29*e1_successor
        assert known_basin_neighbor-actual_third == 14
        assert actual_sixth == p_plus_one-1
        assert research_lifts.step(research_lifts.step(
            research_lifts.step(actual_third))) == actual_sixth
        near_miss = {
            'known_basin_neighbor': known_basin_neighbor,
            'actual_third': actual_third,
            'neighbor_gap': 14,
            'actual_sixth': actual_sixth,
        }
        # A bounded pair of parity words can coalesce on an infinite affine
        # subfamily only if its two slopes differ by powers of 2 and 3.
        # Compute slopes from adjacent symbolic rows, with no target orbit.
        next_data = lower_composite('class95', t+t_stride)
        next_a = next_data['actual_successor']
        current_labels = {'m':m, 'c':data['c'], 'd':data['d'],
                          'b':data['b'], 'x':data['x'], 'z':data['z'],
                          'q1':q1, 'q2':q2, 'e1':e1, 'e2':e2}
        next_labels = {
            'm':next_data['m'], 'c':next_data['c'], 'd':next_data['d'],
            'b':next_data['b'], 'x':next_data['x'], 'z':next_data['z'],
            'q1':(3*next_a-1)//qden,
            'q2':5*(2*next_a-7)//93,
            'e1':(3*next_a+1)//eden,
            'e2':(2*next_a-7)//21,
        }
        def outside_two_three(value):
            for prime in (2,3):
                while value%prime == 0:
                    value //= prime
            return value
        n_slope = next_data['n']-data['n']
        slope_audit = {}
        for label, value in current_labels.items():
            label_slope = next_labels[label]-value
            assert label_slope > 0
            ratio = Fraction(n_slope,label_slope)
            outside = [outside_two_three(ratio.numerator),
                       outside_two_three(ratio.denominator)]
            slope_audit[label] = {
                'label_slope': label_slope,
                'n_to_label_ratio': [ratio.numerator,ratio.denominator],
                'outside_2_3': outside,
                'passes_necessary_condition': outside == [1,1],
            }
        near_miss['coalescence_n_slope'] = n_slope
        near_miss['coalescence_slope_audit'] = slope_audit
        near_miss['bounded_depth_slope_candidates'] = [
            label for label,row in slope_audit.items()
            if row['passes_necessary_condition']]
    return {'variant':variant,'s':s,'t':t,'h':data['h'],'n':data['n'],'m':m,
            'actual_frontier_before':a,'virtual_frontier_before':v,
            'borrowed_inputs':[q1,q2],'output_companions':[e1,e2],
            'actual_frontier_after':a2,'virtual_frontier_after':w,
            'post_six_plus_one':p_plus_one,'odd_run_length':run,
            'common_value_numerator':common.numerator,
            'common_value_denominator':common.denominator,
            'all_auxiliaries_below_m':True,
            'old_restricted_palette_rule':False,
            **near_miss}


def q1_pair_branch(max_depth=11, max_branches=1024):
    """Exact synchronous affine branches for q1(s) and T^7(n)=27*q1(s)+2.

    Each unresolved state covers s=residue+2^exponent*t for every t>=0.
    No individual trajectory is sampled; equality requires both affine
    coefficients to agree on the whole residue progression.
    """
    if not 0 <= max_depth <= 64 or not 1 <= max_branches <= 4096:
        raise ValueError('bounds require 0<=max-depth<=64 and 1<=max-branches<=4096')
    q_slope, q_constant = 2744062650, 1795983881
    initial = {'residue':0, 'exponent':0,
               'q_affine':[q_slope,q_constant],
               'v_affine':[27*q_slope,27*q_constant+2],
               'q_parity_word':'', 'v_parity_word':'',
               'q_odd_steps':0, 'v_odd_steps':0}
    frontier, connections = [initial], []
    completed_depth, status = 0, 'depth_limit'

    def refine(row, bit):
        result = dict(row)
        result['residue'] += (1 << row['exponent'])*bit
        result['exponent'] += 1
        for name in ('q_affine','v_affine'):
            slope, constant = row[name]
            result[name] = [2*slope, constant+bit*slope]
        return result

    def advance(row):
        result = dict(row)
        for name, word, odd_count in (
            ('q_affine','q_parity_word','q_odd_steps'),
            ('v_affine','v_parity_word','v_odd_steps'),
        ):
            slope, constant = row[name]
            assert slope%2 == 0
            parity = constant%2
            result[name] = ([(3*slope)//2,(3*constant+1)//2]
                            if parity else [slope//2,constant//2])
            result[word] += str(parity)
            result[odd_count] += parity
        return result

    for depth in range(1,max_depth+1):
        required = sum(2 if row['q_affine'][0]%2 or row['v_affine'][0]%2
                       else 1 for row in frontier)
        if required > max_branches:
            status = 'branch_limit'
            break
        next_frontier = []
        for row in frontier:
            rows = ([refine(row,0),refine(row,1)]
                    if row['q_affine'][0]%2 or row['v_affine'][0]%2
                    else [row])
            for refined in rows:
                advanced = advance(refined)
                if advanced['q_affine'] == advanced['v_affine']:
                    connections.append({'depth':depth, **advanced})
                else:
                    next_frontier.append(advanced)
        frontier = next_frontier
        completed_depth = depth
        if not frontier:
            status = 'all_coalesced'
            break

    # Equality of nonconstant slopes at equal depth requires three more odd
    # q steps than v steps: their initial slope ratio is 27=3^3.
    assert all(row['q_affine'] != row['v_affine'] for row in frontier)
    assert all(row['q_odd_steps']-row['v_odd_steps'] == 3
               for row in connections)
    return {'q_family':{'slope':q_slope,'constant':q_constant},
            'v_from_q':{'multiplier':27,'offset':2},
            'max_depth':max_depth, 'max_branches':max_branches,
            'completed_depth':completed_depth, 'status':status,
            'connections':connections, 'connection_count':len(connections),
            'first_connection_depth':(connections[0]['depth'] if connections else None),
            'frontier_count':len(frontier), 'frontier':frontier,
            'frontier_exponent_histogram':dict(sorted(Counter(
                row['exponent'] for row in frontier).items()))}


def q1_pair_shadow(k, variant='hard9'):
    """Exact congruence witnesses for bounded q1-family splice tests.

    hard9 separates every n- and q1-prefix through depth k by height.
    carry13 preserves the earlier fixed-point shadow and 15-step descent.
    """
    if not 1 <= k <= 1024:
        raise ValueError('shadow requires 1<=k<=1024')
    q_constant, q_slope = 1795983881, 2744062650
    if variant == 'hard9':
        # (9q(s)+1)/2 has odd slope, so one s residue modulo 2^(k+1)
        # makes 9q+1 divisible by 2^(k+2).  Then T^2(q)=1+2^k*u
        # shadows the 1↔2 cycle, while T^6(n)=18q+1 has k+3 odd steps.
        modulus = 1 << (k+1)
        coefficient = 9*q_slope//2
        constant = (9*q_constant+1)//2
        assert coefficient%2 == 1 and (9*q_constant+1)%2 == 0
        residue = (-constant*pow(coefficient,-1,modulus))%modulus
        q = q_constant+q_slope*residue
        n, remainder = divmod(128*q-1,9)
        assert remainder == 0 and n == 25542881863+39026668800*residue
        nine_q_plus_one = 9*q+1
        u, remainder = divmod(nine_q_plus_one,1 << (k+2))
        assert remainder == 0 and u > 0
        q_after_two = (9*q+5)//4
        post_six = 18*q+1
        q_upper = (27*q+19)//8
        assert q_after_two == 1+(1 << k)*u
        assert post_six+1 == 2*nine_q_plus_one
        assert q_upper < n and q < n < post_six
        return {'variant':'hard9', 'k':k,
                's_residue':residue, 's_modulus':modulus,
                's_witness':residue, 'n':n, 'q':q, 'v':27*q+2,
                'nine_q_plus_one':nine_q_plus_one,
                'cycle_shadow_u':u, 'q_after_two':q_after_two,
                'q_prefix_upper_bound':q_upper, 'n_post_six':post_six,
                'n_above_start_steps_at_least':k+9,
                'q_below_n_through':k,
                'no_lagged_meeting_depths_through':k}
    if variant != 'carry13':
        raise ValueError('variant must be hard9 or carry13')
    exponent = max(k,8)
    modulus = 1 << (exponent-1)
    coefficient = 13*q_slope//2
    constant = (13*q_constant+1)//2
    assert coefficient%2 == 1 and (13*q_constant+1)%2 == 0
    residue = (-constant*pow(coefficient,-1,modulus))%modulus
    base_q = q_constant+q_slope*residue
    bound = 19*6**k
    q_increment = q_slope*modulus
    shift = max(0,(bound-base_q)//q_increment+1)
    s = residue+modulus*shift
    q = q_constant+q_slope*s
    v = 27*q+2
    n, remainder = divmod(128*q-1,9)
    assert remainder == 0 and n == 25542881863+39026668800*s
    assert q > bound and (13*q+1)%(1 << exponent) == 0
    assert (v-q)%(1 << (exponent+1)) == 0
    assert 0 < q < v and q%2 == v%2 == 1
    # For q ≡ -1/13 (mod 256), both q and v have parity word 11011000.
    # T^8(v)=(81v+85)/256=(19683n+33803)/32768, below n for n>=3.
    assert q%256 == v%256 == 59
    endpoint, remainder = divmod(19683*n+33803,32768)
    assert remainder == 0 and endpoint < n
    # For any i,j<=k, a nonresonant equality T^i(n)=T^j(q) would force
    # q<=19*6^k from the exact affine word offsets.  The only equal-slope
    # case has i=j+7 and reduces to T^j(27q+2)=T^j(q), ruled out by shadow.
    return {'variant':'carry13', 'k':k, 'shadow_exponent':exponent,
            's_residue':residue, 's_modulus':modulus,
            's_shift':shift, 's_witness':s,
            'n':n, 'q':q, 'v':v, 'difference':v-q,
            'nonresonant_q_bound':bound,
            'fixed_point_numerator':13*q+1,
            'same_parity_steps_at_least':k,
            'no_synchronous_meeting_through':k,
            'no_lagged_meeting_depths_through':k,
            'fifteen_step_parity_word':'111010111011000',
            'fifteen_step_endpoint':endpoint,
            'strict_descent_at_fifteen':True}


def q1_phase_exit(length, u):
    """Exact regular phase plus two exit steps for a positive affine pair.

    The pair need not come from the hard q1 family; membership is reported.
    This diagnoses a candidate rank and makes no convergence assertion.
    """
    if not 2 <= length <= 1024 or u <= 0 or u%2 == 0:
        raise ValueError('phase-exit requires 2<=L<=1024 and positive odd u')
    r = (length-2)//2
    three_r, nine_r = 3**r, 9**r
    w = three_r*u
    initial_a = (1 << (length+1))*u-1
    initial_b = 1+(1 << (length-2))*u
    if length%2:
        exit_a, exit_b = 16*nine_r*u-1, 1+2*w
        final_a, final_b = 36*nine_r*u-1, (9*w+7)//2
    else:
        exit_a, exit_b = 8*nine_r*u-1, 1+w
        final_a = 18*nine_r*u-1
        final_b = ((w+1)//4 if w%4 == 3 else (3*w+5)//4)
    multiplier = 8*three_r
    assert exit_a+1 == multiplier*(exit_b-1)

    def reentry(a, b):
        if b <= 1 or (a+1)%(b-1):
            return {'holds':False, 'j':None, 'multiplier':None}
        quotient = (a+1)//(b-1)
        if quotient%8:
            return {'holds':False, 'j':None, 'multiplier':None}
        power, j = quotient//8, 0
        while power > 1 and power%3 == 0:
            power //= 3
            j += 1
        return {'holds':power == 1,
                'j':j if power == 1 else None,
                'multiplier':quotient if power == 1 else None}

    def state(a, b):
        assert a > 0 and b > 0
        return {'A':a, 'B':b, 'R':(a+1)*(b-1)**3,
                'reentry_8_times_power3':reentry(a,b)}

    initial = state(initial_a,initial_b)
    phase_exit = state(exit_a,exit_b)
    final = state(final_a,final_b)
    assert initial['reentry_8_times_power3']['j'] == 0
    assert phase_exit['reentry_8_times_power3']['j'] == r
    if length%2:
        # Final J=(A+1)/(B-1)=M*9w/(9w+5) lies strictly between M/3
        # and M, where M=8*3^r.  No multiplier 8*3^j lies there.
        assert multiplier*(final_b-1) > final_a+1
        assert 3*(final_a+1) > multiplier*(final_b-1)
        assert not final['reentry_8_times_power3']['holds']

    raw_a, raw_b = initial_a, initial_b
    a_bits, b_bits = [], []
    for step_index in range(2*r+2):
        if step_index == 2*r:
            assert (raw_a,raw_b) == (exit_a,exit_b)
        a_bits.append(str(raw_a%2))
        b_bits.append(str(raw_b%2))
        raw_a,raw_b = research_lifts.step(raw_a),research_lifts.step(raw_b)
    assert (raw_a,raw_b) == (final_a,final_b)

    q_numerator = (1 << length)*u-1
    q_integral = q_numerator%9 == 0
    q = q_numerator//9 if q_integral else None
    q_constant,q_slope = 1795983881,2744062650
    in_family = (q_integral and q >= q_constant and
                 (q-q_constant)%q_slope == 0)
    s = (q-q_constant)//q_slope if in_family else None
    n = (128*q-1)//9 if in_family else None
    if in_family:
        assert n == 25542881863+39026668800*s
        assert initial_a == 18*q+1 and initial_b == (9*q+5)//4

    def ratio(numerator, denominator):
        value = Fraction(numerator,denominator)
        return [value.numerator,value.denominator]

    odd_identity = None
    if length%2:
        lhs, rhs = 2*(final_a+1), multiplier*(2*final_b-7)
        assert lhs == rhs
        odd_identity = {'lhs':lhs, 'rhs':rhs, 'holds':True}
    return {'L':length, 'u':u, 'regular_two_step_blocks':r,
            'regular_steps':2*r, 'exit_steps':2, 'M':multiplier,
            'family_membership':{'q_integral':q_integral, 'q':q,
                                 'in_hard_q1_family':in_family,
                                 's':s, 'n':n},
            'initial':initial, 'phase_exit':phase_exit, 'final':final,
            'rank_ratios':{
                'exit_over_initial':ratio(phase_exit['R'],initial['R']),
                'final_over_exit':ratio(final['R'],phase_exit['R']),
                'final_over_initial':ratio(final['R'],initial['R'])},
            'odd_L_affine_identity':odd_identity,
            'raw_iteration_checked':True,
            'raw_parity_words':{'A':''.join(a_bits),'B':''.join(b_bits)}}


def q1_run_exit(length, u):
    """Follow an odd phase exit through two odd steps and all forced halves.

    This follows only a symbolic, finite local run.  X versus u is diagnostic;
    it is not a certificate for the original target's convergence.
    """
    if length < 3 or length > 1023 or length%2 == 0 or u <= 0 or u%2 == 0:
        raise ValueError('run-exit requires odd 3<=L<=1023 and positive odd u')
    phase = q1_phase_exit(length,u)
    exit_a = phase['final']['A']
    h = 3**((length+1)//2)
    even_start = h*h*u-1
    first_odd_step = research_lifts.step(exit_a)
    second_odd_step = research_lifts.step(first_odd_step)
    assert exit_a%2 == first_odd_step%2 == 1
    assert second_odd_step == even_start and even_start%2 == 0
    x, even_steps = even_start, 0
    while x%2 == 0:
        x //= 2
        even_steps += 1
    assert x > 0 and x%2 == 1
    raw = second_odd_step
    for _ in range(even_steps):
        assert raw%2 == 0
        raw = research_lifts.step(raw)
    assert raw == x and (h*h*u-1) == (1 << even_steps)*x
    membership = phase['family_membership']
    def compare(a,b):
        return 'shrink' if a < b else 'grow' if a > b else 'equal'
    return {'L':length, 'u':u, 'H':h,
            'phase_regular_blocks':phase['regular_two_step_blocks'],
            'phase_exit_final':phase['final'],
            'family_membership':membership,
            'forced_odd_prefix':[exit_a,first_odd_step,even_start],
            'k_even_steps':even_steps,
            'X':x, 'X_vs_u':compare(x,u),
            'X_vs_n':(compare(x,membership['n'])
                      if membership['in_hard_q1_family'] else None),
            'raw_iteration_checked':True}


def q1_offset_trace(r, u, steps):
    """Exact inherited relation under paired shortcut steps, with admission.

    The signed relation h*A-k*B=c is updated from parity coefficients before
    checking the independently iterated vertices.  Negative u is an algebraic
    control and cannot certify a positive Collatz connection.
    """
    if not 0 <= r <= 128 or u == 0 or u%2 == 0 or not 0 <= steps <= 1024:
        raise ValueError('offset-trace needs 0<=r<=128, nonzero odd u, 0<=steps<=1024')
    a = 36*9**r*u-1
    b_vertex = (9*3**r*u+7)//2
    exponent = r
    h, k, c = 1, 8*3**r, -28*3**r-1
    assert h*a-k*b_vertex == c

    # A word w of three shortcut parities has T_w(A)=(3^ones*A+beta)/8.
    # Its terminal coefficient relation is 3^ones*A-8*B=-beta.  Matching
    # those coefficients is sufficient only when w is the admitted word.
    terminal_table = []
    for mask in range(8):
        word = format(mask,'03b')
        beta = 0
        for index,letter in enumerate(word):
            if letter == '1':
                beta = 3*beta+(1 << index)
        terminal_table.append({'word':word,'h':3**word.count('1'),
                               'k':8,'c':-beta,'beta':beta})

    history = []
    for index in range(steps+1):
        assert h*a-k*b_vertex == c and c%2 == a%2
        actual_word, after_three = '', a
        for _ in range(3):
            actual_word += str(after_three%2)
            after_three = research_lifts.step(after_three)
        point_words = [row['word'] for row in terminal_table
                       if row['h']*a-row['k']*b_vertex == row['c']]
        coefficient_words = [row['word'] for row in terminal_table
                             if (h,k,c) == (row['h'],row['k'],row['c'])]
        actual_three = after_three == b_vertex
        assert (actual_word in point_words) == actual_three
        assert not (actual_word in coefficient_words) or actual_three
        history.append({
            'step':index, 'A':a, 'B':b_vertex,
            'b':exponent, 'h':h, 'k':k, 'c':c,
            'A_parity':a%2, 'B_parity':b_vertex%2,
            'actual_three_word':actual_word,
            'terminal_point_words':point_words,
            'terminal_coefficient_words':coefficient_words,
            'terminal_A_equals_B':a == b_vertex,
            'terminal_T3A_equals_B':actual_three,
            'positive_A_equals_B':a == b_vertex and a > 0,
            'positive_T3A_equals_B':actual_three and a > 0 and b_vertex > 0,
        })
        if index == steps:
            break
        parity_a, parity_b = a%2, b_vertex%2
        multiplier_a, multiplier_b = (3 if parity_a else 1), (3 if parity_b else 1)
        next_exponent = exponent+parity_a-parity_b
        next_h = 3**max(-next_exponent,0)
        next_k = 8*3**max(next_exponent,0)
        next_c = (Fraction(next_h*multiplier_a*c,2*h) +
                  Fraction(next_h*parity_a-next_k*parity_b,2))
        assert next_c.denominator == 1
        a, b_vertex = research_lifts.step(a), research_lifts.step(b_vertex)
        exponent,h,k,c = next_exponent,next_h,next_k,next_c.numerator

    if u > 0:
        phase = q1_phase_exit(2*r+3,u)
        assert (history[0]['A'],history[0]['B']) == (
            phase['final']['A'],phase['final']['B'])
        membership = phase['family_membership']
    else:
        membership = {'q_integral':False,'q':None,
                      'in_hard_q1_family':False,'s':None,'n':None}
    return {'r':r,'u':u,'steps':steps,
            'positive_start':u > 0,
            'family_membership':membership,
            'terminal_three_step_table':terminal_table,
            'history':history,
            'positive_A_equals_B_steps':[row['step'] for row in history
                                         if row['positive_A_equals_B']],
            'positive_T3A_equals_B_steps':[row['step'] for row in history
                                           if row['positive_T3A_equals_B']],
            'c_crossings_nonpositive_to_positive':[
                current['step'] for previous,current in zip(history,history[1:])
                if previous['c'] <= 0 < current['c']]}


def q1_offset_ray(depth):
    """One hard-family 2-adic ray with K inherited six-step blocks.

    The output is a finite exact prefix and its arithmetic checkpoint ledger,
    not a full-orbit or convergence assertion.
    """
    if not 0 <= depth <= 128:
        raise ValueError('offset-ray requires 0<=K<=128')
    u0, slope_half = 23629975235, 12348281925
    exponent = 12+6*depth
    modulus = 1 << (exponent-1)
    constant = (9*u0+1)//2
    coefficient = 9*slope_half
    assert coefficient%2 == 1
    t = (-constant*pow(coefficient,-1,modulus))%modulus
    u = u0+2*slope_half*t
    s = 7+8*t
    horizon = 9+6*depth
    assert (9*u+1)%(1 << exponent) == 0
    trace = q1_offset_trace(0,u,horizon)
    membership = trace['family_membership']
    assert membership['in_hard_q1_family'] and membership['s'] == s
    n,q = membership['n'],membership['q']
    history = trace['history']
    initial_a = 36*u-1
    assert history[0]['A'] == initial_a and initial_a > n
    assert all(row['A'] >= initial_a and row['B'] < n for row in history)
    checkpoints = []
    for index in range(depth+1):
        position = 9+6*index
        row = history[position]
        multiplier = 72*3**index
        assert (row['b'],row['h'],row['k'],row['c']) == (
            2+index,1,multiplier,-multiplier-5)
        assert row['A']+1 == multiplier*(row['B']-1)-4
        checkpoints.append({'block':index, 'step':position,
                            'A':row['A'], 'B':row['B'],
                            'b':row['b'], 'h':row['h'],
                            'k':row['k'], 'c':row['c'],
                            'm':multiplier, 'd':-4})
        if index < depth:
            block = history[position:position+6]
            assert ''.join(str(part['A_parity']) for part in block) == '110110'
            assert ''.join(str(part['B_parity']) for part in block) == '101010'

    original_n = [n]
    original_q = [q]
    for _ in range(8+horizon):
        original_n.append(research_lifts.step(original_n[-1]))
    for _ in range(4+horizon):
        original_q.append(research_lifts.step(original_q[-1]))
    assert all(original_n[8+i] == row['A'] and
               original_q[4+i] == row['B']
               for i,row in enumerate(history))
    assert all(value >= n for value in original_n)
    assert all(value < n for value in original_q)
    return {'K':depth, 'P':exponent, 't_residue':t,
            't_modulus':modulus, 's':s, 'u':u,
            'n':n, 'q':q, 'trace_horizon':horizon,
            'checkpoints':checkpoints,
            'six_step_words':{'A':'110110','B':'101010'},
            'verified_six_step_blocks':depth,
            'postexit_bounds':{'A_min':min(row['A'] for row in history),
                               'initial_A':initial_a,
                               'B_max':max(row['B'] for row in history),
                               'A_ge_initial_gt_n':True,'B_lt_n':True},
            'original_prefix_bounds':{'n_min':min(original_n),
                                      'q_max':max(original_q),
                                      'n_ge_start':True,'q_lt_n':True}}


def q1_ray_exit(j, e, v):
    """Exact finite exit from the negative/positive reference shadow.

    This only follows e+4 shortcut steps.  The reference cycles are
    (-5,-7,-10) and (1,2); their parity words agree with the actual pair
    only up to the independently recorded first mismatch indices.
    """
    if not 0 <= j <= 128 or not 0 <= e <= 512 or v <= 0 or v%2 == 0:
        raise ValueError('ray-exit needs 0<=j<=128, 0<=e<=512, positive odd v')

    a = 72*3**j*(1 << e)*v-5
    b_vertex = (1 << e)*v+1
    initial_a, initial_b = a, b_vertex
    multiplier, defect = Fraction(72*3**j), Fraction(-4)
    a_reference, b_reference = (-5,-7,-10), (1,2)
    first_mismatch = {'A':None, 'B':None}
    checkpoint_indices = {
        'initial':0, 'B_first_mismatch':e, 'B_after_mismatch':e+1,
        'A_first_mismatch':e+3, 'final':e+4,
    }
    checkpoints = {}
    parities_a, parities_b = [], []

    def offset(value, reference):
        difference = value-reference
        return {'difference':difference, 'reference_hit':difference == 0,
                'v2':None if difference == 0 else
                     (abs(difference) & -abs(difference)).bit_length()-1}

    for index in range(e+5):
        ref_a, ref_b = a_reference[index%3], b_reference[index%2]
        assert Fraction(a+1) == multiplier*(b_vertex-1)+defect
        if index <= e:
            assert b_vertex == ref_b + 3**((index+1)//2)*(1 << (e-index))*v
        if index <= e+3:
            assert a == ref_a + 9*3**j*3**(index-index//3)*(
                1 << (e+3-index))*v
        if first_mismatch['A'] is None and a%2 != ref_a%2:
            first_mismatch['A'] = index
        if first_mismatch['B'] is None and b_vertex%2 != ref_b%2:
            first_mismatch['B'] = index
        for name, position in checkpoint_indices.items():
            if position == index:
                checkpoints[name] = {
                    'index':index, 'A':a, 'B':b_vertex,
                    'm':[multiplier.numerator,multiplier.denominator],
                    'd':[defect.numerator,defect.denominator],
                    'A_reference':ref_a, 'B_reference':ref_b,
                    'A_offset':offset(a,ref_a),
                    'B_offset':offset(b_vertex,ref_b),
                }
        if index == e+4:
            break
        parity_a, parity_b = a%2, b_vertex%2
        parities_a.append(parity_a)
        parities_b.append(parity_b)
        alpha, beta = (3 if parity_a else 1), (3 if parity_b else 1)
        old_intercept = defect-multiplier-1
        next_multiplier = multiplier*alpha/beta
        next_intercept = (alpha*old_intercept+parity_a-
                          next_multiplier*parity_b)/2
        multiplier = next_multiplier
        defect = next_intercept+multiplier+1
        a, b_vertex = research_lifts.step(a), research_lifts.step(b_vertex)

    assert first_mismatch == {'A':e+3,'B':e}
    def compare(final, initial):
        return 'grow' if final > initial else 'shrink' if final < initial else 'equal'
    return {'j':j, 'e':e, 'v':v,
            'initial':{'A':initial_a,'B':initial_b,'m':72*3**j,'d':-4},
            'steps':e+4, 'shared_phase_steps':e,
            'complete_six_blocks':e//6,
            'first_parity_mismatch':first_mismatch,
            'checkpoints':checkpoints,
            'A_parity_word':''.join(map(str,parities_a)),
            'B_parity_word':''.join(map(str,parities_b)),
            'final_vs_initial':{'A':compare(a,initial_a),
                                'B':compare(b_vertex,initial_b)},
            'shadow_formulas_checked':True,
            'inherited_relation_checked':True}


def q1_ray_refill(depth, odd_part_mod64=None):
    """One exact six-step fuel refill in an actual hard-family residue class.

    This is a finite prefix constructor.  It does not assert a future return
    after the newly supplied K two-adic fuel steps.
    """
    if not 0 <= depth <= 128:
        raise ValueError('ray-refill needs 0<=K<=128')
    if odd_part_mod64 is not None and not (
            1 <= odd_part_mod64 <= 63 and odd_part_mod64%2 == 1):
        raise ValueError('odd-part-mod64 needs odd R in 1..63')
    u0, half_slope = 23629975235, 12348281925
    base_t, t_stride = 1690, 2048
    base_u = u0+2*half_slope*base_t
    base = q1_offset_trace(0,base_u,9)
    base_history = base['history']
    assert ''.join(str(row['A_parity']) for row in base_history[:9]) == '110110110'
    assert ''.join(str(row['B_parity']) for row in base_history[:9]) == '110001010'
    base_v = base_history[9]['B']-1
    assert base_history[9]['A'] == 72*base_v-5 and base_v%2 == 1
    v_slope = 4*3**6*half_slope
    constant = (9*base_v+1)//4
    odd_slope = 9*v_slope//4
    assert (9*base_v+1)%4 == 0 and odd_slope%2 == 1
    modulus = 1 << (depth+(10 if odd_part_mod64 is not None else 5))
    desired = 1 if odd_part_mod64 is None else odd_part_mod64
    z = ((desired << (depth+4))-constant)*pow(odd_slope,-1,modulus)%modulus
    t = base_t+t_stride*z
    u = u0+2*half_slope*t
    v = base_v+v_slope*z
    assert (9*v+1)%(1 << (depth+6)) == 0
    assert (9*v+1)%(1 << (depth+7)) != 0

    trace = q1_offset_trace(0,u,9)
    history = trace['history']
    assert ''.join(str(row['A_parity']) for row in history[:9]) == '110110110'
    assert ''.join(str(row['B_parity']) for row in history[:9]) == '110001010'
    entry = history[9]
    assert (entry['A'],entry['B'],entry['b'],entry['c']) == (
        72*v-5,v+1,2,-77)
    a,b_vertex = entry['A'],entry['B']
    a_path,b_path = [a],[b_vertex]
    for _ in range(6):
        a,b_vertex = research_lifts.step(a),research_lifts.step(b_vertex)
        a_path.append(a)
        b_path.append(b_vertex)
    assert ''.join(str(x%2) for x in a_path[:-1]) == '110010'
    assert ''.join(str(x%2) for x in b_path[:-1]) == '000101'
    assert (a,b_vertex) == ((243*v-13)//8,(9*v+65)//64)
    assert a+1 == 216*(b_vertex-1)-4
    new_fuel = b_vertex-1
    assert new_fuel > 0 and (new_fuel & -new_fuel).bit_length()-1 == depth

    membership = trace['family_membership']
    assert membership['in_hard_q1_family'] and membership['s'] == 7+8*t
    n,q = membership['n'],membership['q']
    n_path,q_path = [n],[q]
    for _ in range(23):
        n_path.append(research_lifts.step(n_path[-1]))
    for _ in range(19):
        q_path.append(research_lifts.step(q_path[-1]))
    assert (n_path[17],q_path[13]) == (entry['A'],entry['B'])
    assert (n_path[23],q_path[19]) == (a,b_vertex)
    assert all(value >= n for value in n_path)
    assert all(value < n for value in q_path)

    # The six-step refill supplies a new two-adic shadow phase.  Follow it
    # through both first parity disagreements, without assuming a later reset.
    odd_v = new_fuel >> depth
    assert odd_v > 0 and odd_v%2 == 1
    if odd_part_mod64 is not None:
        assert odd_v%64 == odd_part_mod64
    following = q1_ray_exit(1,depth,odd_v)
    assert following['initial']['A'] == a
    assert following['initial']['B'] == b_vertex
    complete_blocks = depth//6
    last_block_step = 6*complete_blocks
    block_a,block_b = a,b_vertex
    for _ in range(last_block_step):
        block_a = research_lifts.step(block_a)
        block_b = research_lifts.step(block_b)
    block_denominator = 64**complete_blocks
    assert ((a+5)*81**complete_blocks)%block_denominator == 0
    assert ((b_vertex-1)*27**complete_blocks)%block_denominator == 0
    assert block_a+5 == (a+5)*81**complete_blocks//block_denominator
    assert block_b-1 == (b_vertex-1)*27**complete_blocks//block_denominator
    block_multiplier = 216*3**complete_blocks
    assert block_a+1 == block_multiplier*(block_b-1)-4
    assert (block_b-1 & -(block_b-1)).bit_length()-1 == depth%6
    zero_fuel_six = None
    if depth == 0:
        next_a,next_b = a,b_vertex
        word_a,word_b = '', ''
        for _ in range(6):
            word_a += str(next_a%2)
            word_b += str(next_b%2)
            next_a = research_lifts.step(next_a)
            next_b = research_lifts.step(next_b)
        same_j1_relation = next_a+1 == 216*(next_b-1)-4
        if odd_v%64 == 45:
            assert same_j1_relation and next_a < n
        zero_fuel_six = {
            'A':next_a,'B':next_b,'A_word':word_a,'B_word':word_b,
            'same_j1_relation':same_j1_relation,
            'A_below_original_n':next_a < n,
            'original_n_step':29,'original_q_step':25}
    def compare(x,y):
        return 'grow' if x>y else 'shrink' if x<y else 'equal'
    return {
        'K':depth,'requested_odd_part_mod64':odd_part_mod64,
        't':t,'t_base':base_t,'t_stride':t_stride,
        'z_residue':z,'z_modulus':modulus,
        'u':u,'v':v,'v_base':base_v,'v_slope':v_slope,
        's':membership['s'],'n':n,'q':q,
        'nine_v_plus_one_v2':depth+6,
        'entry':{'A':entry['A'],'B':entry['B'],'m':72,'d':-4,
                 'original_n_step':17,'original_q_step':13},
        'six_step_words':{'A':'110010','B':'000101'},
        'exit':{'A':a,'B':b_vertex,'m':216,'d':-4,
                'new_fuel_v2':depth,
                'original_n_step':23,'original_q_step':19},
        'growth':{'A':compare(a,entry['A']),
                  'B':compare(b_vertex,entry['B'])},
        'following_phase':{
            'odd_V':odd_v,
            'odd_V_mod64':odd_v%64,
            'ordinary_six_block_available':depth >= 6,
            'j1_six_return_residue45':odd_v%64 == 45,
            'post_zero_fuel_six':zero_fuel_six,
            'complete_six_blocks':complete_blocks,
            'last_six_block_endpoint':{
                'index':last_block_step,'A':block_a,'B':block_b,
                'j':1+complete_blocks,'m':block_multiplier,'d':-4,
                'remaining_fuel':depth%6,
                'A_vs_pre_refill_entry':compare(block_a,entry['A']),
                'B_vs_pre_refill_entry':compare(block_b,entry['B'])},
            'first_parity_mismatch':following['first_parity_mismatch'],
            'at_B_first_mismatch':following['checkpoints']['B_first_mismatch'],
            'at_A_first_mismatch':following['checkpoints']['A_first_mismatch'],
            'at_end':following['checkpoints']['final'],
            'steps':following['steps'],
            'end_vs_return':following['final_vs_initial'],
        },
        'original_prefix_bounds':{
            'n_min':min(n_path),'q_max':max(q_path),
            'n_ge_start_through_23':True,'q_lt_n_through_19':True},
        'raw_iterates_checked':True}


def oriented_rules(witness_path):
    data = json.loads(Path(witness_path).read_text())
    if not isinstance(data.get('witness'), list):
        raise ValueError('witness file must contain a signed quadratic witness list')
    rules = Counter()
    for row in data['witness']:
        left, right = tuple(row['remove']), tuple(row['insert'])
        coefficient = row['coefficient']
        if not coefficient:
            raise ValueError('zero-coefficient witness row')
        if coefficient < 0:
            left, right = right, left
        rules[(left, right)] += abs(coefficient)
    return rules


def target_tail(base_n, other_n):
    base_orbit = research_lifts.orbit_to_one(base_n)
    other_orbit = research_lifts.orbit_to_one(other_n)
    base_index = {u: i for i, u in enumerate(base_orbit)}
    other_i = next(i for i, u in enumerate(other_orbit) if u in base_index)
    join = other_orbit[other_i]
    base_i = base_index[join]
    assert other_orbit[other_i:] == base_orbit[base_i:]
    return {'base_n': base_n, 'other_n': other_n,
            'target_tail_join': join,
            'target_tail_join_steps_other_base': [other_i, base_i],
            'shared_target_tail_steps': len(other_orbit)-1-other_i}


def compare_witnesses(base_n, base_path, other_n, other_path):
    base, other = oriented_rules(base_path), oriented_rules(other_path)
    shared = base.keys() & other.keys()
    tail = target_tail(base_n, other_n)
    distinguished = {
        'virtual_first_5n': 5*other_n,
        'virtual_second': (15*other_n+1)//2,
        'actual_first_n': other_n,
    }
    touches = {}
    for name, label in distinguished.items():
        rows = [(left, right, coefficient) for (left, right), coefficient in other.items()
                if label in left+right]
        touches[name] = {'label': label, 'unique_oriented_rules': len(rows),
                         'weighted_applications': sum(row[2] for row in rows)}
    return {**tail,
            'base_unique_oriented_Q_rules': len(base),
            'other_unique_oriented_Q_rules': len(other),
            'shared_unique_oriented_Q_rules': len(shared),
            'shared_weighted_applications': sum(min(base[r], other[r]) for r in shared),
            'distinguished_label_rule_touches': touches}


def family_table():
    rows = []
    seen = {}
    for family, cases in (
        ('plus', [(j, 2**j+7) for j in range(6,17)]),
        ('minus', [(j, 2**j-57) for j in range(6,17)]),
        ('holdout', [(k, 64*k+7) for k in (2,3,5,9,17)]),
        ('growth', [(j, long_growth(j)['n']) for j in (2,4,6,8,10,12,16,20)]),
    ):
        for parameter, n in cases:
            if n in seen:
                rows[seen[n]]['aliases'].append([family, parameter])
                continue
            row = profile(n)
            seen[n] = len(rows)
            rows.append({'family': family, 'parameter': parameter, 'aliases': [], 'n': n,
                         'actual_steps': row['actual_steps'],
                         'meeting_steps_actual_smaller': row['meeting_steps_actual_smaller'],
                         'meeting_value': row['meeting_value'],
                         'shared_tail_steps': row['shared_tail_steps'],
                         'initial_parity_16': row['actual_prefix_parity_to_meeting'][:16],
                         'residual_actual_labels': len(row['actual_only_odd_labels']),
                         'residual_virtual_labels': len(row['virtual_only_odd_labels']),
                         'forced_net_moves': row['forced_net_moves'],
                         'three_divisible_label_difference': row['three_divisible_label_difference']})
    return {'rows': rows,
            'symbolic_controls': [fixed_offset_descent('plus', j) for j in (11,12,16)] +
                                 [fixed_offset_descent('minus', j) for j in (8,9,16)],
            'long_growth_controls': [long_growth(j) for j in (2,4,6,8,10,12,16,20)]}


def main():
    if sys.argv[1:] == ['test']:
        raise SystemExit(subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                          'python3', '-m', 'pytest',
                                          str(Path(__file__).with_name('test_repair_family.py')), '-q']))
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    one = sub.add_parser('profile')
    one.add_argument('n', type=int)
    formula = sub.add_parser('descent')
    formula.add_argument('family', choices=['plus', 'minus'])
    formula.add_argument('j', type=int)
    growth = sub.add_parser('growth')
    growth.add_argument('j', type=int)
    lower = sub.add_parser('lower-prefix')
    lower.add_argument('h', type=int)
    lower_growing = sub.add_parser('lower-growth')
    lower_growing.add_argument('j', type=int)
    composite = sub.add_parser('lower-composite')
    composite.add_argument('family', choices=['class95','class79'])
    composite.add_argument('t', type=int)
    frontier = sub.add_parser('second-frontier-pairs')
    frontier.add_argument('family', choices=['class95','class79'])
    frontier.add_argument('t', type=int)
    frontier.add_argument('--ceiling',choices=['m','n'],default='m')
    cubic = sub.add_parser('second-frontier-cubic')
    cubic.add_argument('s',type=int)
    cubic.add_argument('--variant',choices=['hard64','easy32'],default='hard64')
    pair = sub.add_parser('q1-pair-branch')
    pair.add_argument('--max-depth',type=int,default=11)
    pair.add_argument('--max-branches',type=int,default=1024)
    shadow = sub.add_parser('q1-pair-shadow')
    shadow.add_argument('k',type=int)
    shadow.add_argument('--variant',choices=['hard9','carry13'],default='hard9')
    phase = sub.add_parser('q1-phase-exit')
    phase.add_argument('L',type=int)
    phase.add_argument('u',type=int)
    run_exit = sub.add_parser('q1-run-exit')
    run_exit.add_argument('L',type=int)
    run_exit.add_argument('u',type=int)
    offset = sub.add_parser('q1-offset-trace')
    offset.add_argument('r',type=int)
    offset.add_argument('u',type=int)
    offset.add_argument('--steps',type=int,required=True)
    ray = sub.add_parser('q1-offset-ray')
    ray.add_argument('K',type=int)
    ray_exit = sub.add_parser('q1-ray-exit')
    ray_exit.add_argument('j',type=int)
    ray_exit.add_argument('e',type=int)
    ray_exit.add_argument('v',type=int)
    refill = sub.add_parser('q1-ray-refill')
    refill.add_argument('K',type=int)
    refill.add_argument('--odd-part-mod64',type=int)
    comparison = sub.add_parser('compare')
    comparison.add_argument('base_n', type=int)
    comparison.add_argument('base_witness')
    comparison.add_argument('other_n', type=int)
    comparison.add_argument('other_witness')
    tail = sub.add_parser('target-tail')
    tail.add_argument('base_n', type=int)
    tail.add_argument('other_n', type=int)
    sub.add_parser('family')
    args = parser.parse_args()
    result = (profile(args.n) if args.command == 'profile' else
              fixed_offset_descent(args.family, args.j) if args.command == 'descent' else
              long_growth(args.j) if args.command == 'growth' else
              lower_prefix(args.h) if args.command == 'lower-prefix' else
              lower_growth(args.j) if args.command == 'lower-growth' else
              lower_composite(args.family,args.t) if args.command == 'lower-composite' else
              second_frontier_pairs(args.family,args.t,args.ceiling) if args.command == 'second-frontier-pairs' else
              second_frontier_cubic(args.s,args.variant) if args.command == 'second-frontier-cubic' else
              q1_pair_branch(args.max_depth,args.max_branches) if args.command == 'q1-pair-branch' else
              q1_pair_shadow(args.k,args.variant) if args.command == 'q1-pair-shadow' else
              q1_phase_exit(args.L,args.u) if args.command == 'q1-phase-exit' else
              q1_run_exit(args.L,args.u) if args.command == 'q1-run-exit' else
              q1_offset_trace(args.r,args.u,args.steps) if args.command == 'q1-offset-trace' else
              q1_offset_ray(args.K) if args.command == 'q1-offset-ray' else
              q1_ray_exit(args.j,args.e,args.v) if args.command == 'q1-ray-exit' else
              q1_ray_refill(args.K,args.odd_part_mod64) if args.command == 'q1-ray-refill' else
              compare_witnesses(args.base_n, args.base_witness, args.other_n,
                                args.other_witness) if args.command == 'compare' else
              target_tail(args.base_n, args.other_n) if args.command == 'target-tail' else
              family_table())
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
