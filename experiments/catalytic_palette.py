#!/usr/bin/env -S uv run --quiet python3
"""Exact, finite controls for the catalytic certificate palette.

``./catalytic_palette.py test`` delegates to the external pytest suite.
The relation ledger is a necessary condition for a repair, not a path finder.
The closure uses quadratic exchanges after unit seeding; it does not claim
completeness for all uses of the essential cubic.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess
import sys

LIFTS = Path(__file__).with_name('research_lifts.py')
spec = importlib.util.spec_from_file_location('research_lifts', LIFTS)
assert spec and spec.loader
research = importlib.util.module_from_spec(spec)
spec.loader.exec_module(research)

UNIT8 = Counter([19, 25, 29, 55, 83])
UNIT13 = Counter([5, 7, 7, 11, 17, 55, 65, 83])
CUBIC_LEFT = Counter([5, 55, 83])
CUBIC_RIGHT = Counter([11, 13, 17])


def nonzero(vector):
    return {key: value for key, value in vector.items() if value}


def subtract_scaled(vector, other, scale):
    for key, value in other.items():
        updated = vector.get(key, 0) - scale*value
        if updated:
            vector[key] = updated
        else:
            vector.pop(key, None)


class IntegerRelationBasis:
    """Sparse integer row lattice with Euclidean pivot reduction.

    Every row carries its exact integer combination of input rules.  The
    Euclidean swaps are unimodular, so basis reductions never replace the
    integer lattice with its rational span.
    """

    def __init__(self, preferred=()):
        self.rows = {}
        self.preferred = set(preferred)

    def pivot(self, vector):
        return max(vector, key=lambda label: (label in self.preferred, label))

    def add(self, vector, combination):
        vector, combination = nonzero(vector), nonzero(combination)
        while vector:
            pivot = self.pivot(vector)
            if pivot not in self.rows:
                if vector[pivot] < 0:
                    vector = {k: -v for k, v in vector.items()}
                    combination = {k: -v for k, v in combination.items()}
                self.rows[pivot] = (vector, combination)
                return
            base, base_combination = self.rows[pivot]
            quotient = vector[pivot] // base[pivot]
            subtract_scaled(vector, base, quotient)
            subtract_scaled(combination, base_combination, quotient)
            if vector.get(pivot, 0):
                # The strictly smaller Euclidean remainder becomes the pivot.
                old_base = (base, base_combination)
                if vector[pivot] < 0:
                    vector = {k: -v for k, v in vector.items()}
                    combination = {k: -v for k, v in combination.items()}
                self.rows[pivot] = (vector, combination)
                vector, combination = old_base

    def express(self, vector):
        """Return exact integer rule coefficients, or the nonzero remainder."""
        vector = nonzero(vector)
        combination = {}
        while vector:
            pivot = self.pivot(vector)
            if pivot not in self.rows:
                break
            base, base_combination = self.rows[pivot]
            quotient, remainder = divmod(vector[pivot], base[pivot])
            if remainder:
                break
            subtract_scaled(vector, base, quotient)
            subtract_scaled(combination, base_combination, -quotient)
        return combination, vector


def quadratic_residual(n):
    data = research.wild_five_repair(n)
    actual = counts(data['actual_path'])[1]
    virtual = counts(data['virtual_prefix'] + data['smaller_path'][1:])[1]
    virtual.update([7, 7, 11, 17, 55, 65, 83])
    result = dict(actual)
    subtract_scaled(result, virtual, 1)
    forced = palette_ledger(n)['forced_net_moves']
    subtract_scaled(result, {1:1}, forced['U2'])
    subtract_scaled(result, UNIT8, forced['U8'])
    subtract_scaled(result, UNIT13, forced['U13'])
    subtract_scaled(result, CUBIC_RIGHT, forced['cubic_forward'])
    subtract_scaled(result, CUBIC_LEFT, -forced['cubic_forward'])
    assert sum(result.values()) == 0
    assert result.get(1, 0) == result.get(5, 0) == 0
    return result


def seventy_one_quadratic_residual():
    return quadratic_residual(71)


def pair_vector(before, after):
    vector = dict(Counter(after))
    subtract_scaled(vector, Counter(before), 1)
    return vector


def relation_lattice(n, max_label=3077, all_pairs=False, max_aux_label=100000,
                     neighbor_waves=0, wave_width=10, max_pairs=30000,
                     max_neighbor_source_label=5000, max_rules=5000):
    """A finite *integer* relation search, with exact replayable witnesses.

    Candidate labels are the saved six-round borrowability set plus the known
    path labels.  Restrict all four labels of a relation to that set.  In the
    default targeted mode at least one input label occurs in the residual;
    --all-pairs broadens to every input pair in the finite set.
    """
    closure_path = Path(__file__).with_name('borrowable_palette_71.json')
    closure = json.loads(closure_path.read_text())
    residual = quadratic_residual(n)
    if n % 3 == 0 or any(label % 3 == 0 for label in residual):
        return {'value': n, 'status': 'unsupported-3-divisible-domain',
                'reason': 'borrowable library and quadratic rule filter cover only 3-free labels'}
    target_support = set(residual)
    labels = sorted(u for u in set(closure['known_labels']) | target_support
                    if 1 <= u <= max_label)
    permitted = set(labels)
    if not target_support <= permitted:
        raise ValueError('max_label must include every residual label')
    preferred = set(target_support)
    basis = IntegerRelationBasis(preferred)
    rules = []
    seen_rules = set()
    truncations = set()

    def add_rule(before, after):
        before, after = tuple(sorted(before)), tuple(sorted(after))
        if before == after:
            return False
        if any(label % 3 == 0 for label in before + after):
            return False
        if after < before:
            before, after = after, before
        key = (before, after)
        if key in seen_rules:
            return False
        if len(rules) >= max_rules:
            truncations.add('max_rules')
            return False
        seen_rules.add(key)
        rule = {'remove': list(before), 'insert': list(after)}
        rule_id = len(rules)
        rules.append(rule)
        basis.add(pair_vector(before, after), {rule_id:1})
        return True

    pairs = 0
    for a, b in combinations_with_replacement(labels, 2):
        if len(rules) >= max_rules:
            truncations.add('max_rules')
            break
        if not all_pairs and a not in target_support and b not in target_support:
            continue
        if pairs >= max_pairs:
            truncations.add('max_pairs')
            break
        pairs += 1
        ratio = Fraction(a, research.step(a))*Fraction(b, research.step(b))
        for c, d in research.two_odd_fiber(ratio)['unordered_odd_pairs']:
            if len(rules) >= max_rules:
                truncations.add('max_rules')
                break
            if c not in permitted or d not in permitted:
                continue
            add_rule((a,b),(c,d))
    core_relations = len(rules)
    for label in sorted(target_support):
        if len(rules) >= max_rules:
            truncations.add('max_rules')
            break
        if label > max_neighbor_source_label:
            truncations.add('max_neighbor_source_label')
            continue
        for row in research.quadratic_neighbors(label)['nontrivial_exchanges']:
            if len(rules) >= max_rules:
                truncations.add('max_rules')
                break
            if max(row['before']+row['after']) > max_aux_label:
                continue
            add_rule(row['before'], row['after'])
    combination, remainder = basis.express(residual)
    waves = []
    expanded = set(target_support)
    for wave in range(1, neighbor_waves+1):
        if not remainder or len(rules) >= max_rules:
            break
        chosen = sorted((u for u in remainder if u not in expanded),
                        reverse=True)[:wave_width]
        if not chosen:
            break
        before_count = len(rules)
        for label in chosen:
            if len(rules) >= max_rules:
                truncations.add('max_rules')
                break
            expanded.add(label)
            if label > max_neighbor_source_label:
                truncations.add('max_neighbor_source_label')
                continue
            for row in research.quadratic_neighbors(label)['nontrivial_exchanges']:
                if len(rules) >= max_rules:
                    truncations.add('max_rules')
                    break
                if max(row['before']+row['after']) <= max_aux_label:
                    add_rule(row['before'], row['after'])
        preferred.update(chosen)
        basis = IntegerRelationBasis(preferred)
        for rule_id, rule in enumerate(rules):
            basis.add(pair_vector(rule['remove'], rule['insert']), {rule_id:1})
        combination, remainder = basis.express(residual)
        waves.append({'wave': wave, 'expanded_labels': chosen,
                      'new_relations': len(rules)-before_count,
                      'remainder_size': len(remainder)})
    replay = {}
    for rule_id, scale in combination.items():
        subtract_scaled(replay, pair_vector(rules[rule_id]['remove'],rules[rule_id]['insert']), -scale)
    assert nonzero(replay) == nonzero({k: residual.get(k,0)-remainder.get(k,0) for k in set(residual)|set(remainder)})
    selected = [{'coefficient': coefficient, **rules[rule_id]}
                for rule_id, coefficient in sorted(combination.items()) if coefficient]
    return {'value': n, 'status': 'budget-truncated' if truncations else 'finite-pool-exhausted',
            'truncations': sorted(truncations),
            'candidate_pool': 'saved 71 closure labels plus target residual support; '
                'target-containing input pairs unless all_pairs; Q outputs bounded by max_aux_label',
            'budgets': {'max_pairs': max_pairs, 'max_rules': max_rules,
                        'max_neighbor_source_label': max_neighbor_source_label},
            'mode': 'all-pairs' if all_pairs else 'targeted',
            'max_label': max_label, 'labels': len(labels),
            'max_aux_label': max_aux_label,
            'pairs_evaluated': pairs, 'relations': len(rules),
            'core_relations': core_relations,
            'waves': waves,
            'integer_basis_rank': len(basis.rows),
            'residual': [[k,v] for k,v in sorted(residual.items())],
            'unresolved_remainder': [[k,v] for k,v in sorted(remainder.items())],
            'witness': selected if not remainder else None,
            'partial_combination': selected if remainder else None}


def relation_lattice_71(max_label=3077, all_pairs=False, max_aux_label=100000,
                        neighbor_waves=0, wave_width=10):
    return relation_lattice(71,max_label,all_pairs,max_aux_label,
                            neighbor_waves,wave_width)


def replay_lattice(witness_path, n=None):
    """Independently replay a saved integer witness and construct a catalyst."""
    document = json.loads(Path(witness_path).read_text())
    n = document.get('value',71) if n is None else n
    if document.get('value',n) != n:
        raise ValueError('witness value does not match requested value')
    rules = document['witness']
    if rules is None:
        raise ValueError('saved document has no completed integer witness')
    data = research.wild_five_repair(n)
    virtual = data['virtual_prefix'] + data['smaller_path'][1:]
    source_twos, source_odds = counts(virtual)
    source_twos += 2
    source_odds.update([7,7,11,17,55,65,83])
    target_twos, target_odds = counts(data['actual_path'])
    source = {0: source_twos, **source_odds}
    target = {0: target_twos, **target_odds}
    moves = []

    def append_move(kind, remove, insert, repeats):
        for _ in range(repeats):
            moves.append((kind, dict(remove), dict(insert)))

    forced = palette_ledger(n)['forced_net_moves']
    units = {'U2':{0:1,1:1}, 'U8':{0:3,**UNIT8},
             'U13':{0:5,**UNIT13}}
    for name in ('U2','U8','U13'):
        if forced[name] > 0:
            append_move('insert-'+name, {}, units[name], forced[name])
    if forced['cubic_forward'] > 0:
        append_move('forward-cubic', CUBIC_LEFT, CUBIC_RIGHT,
                    forced['cubic_forward'])
    elif forced['cubic_forward'] < 0:
        append_move('reverse-cubic', CUBIC_RIGHT, CUBIC_LEFT,
                    -forced['cubic_forward'])
    for number, row in enumerate(rules):
        if (len(row['remove']) != 2 or len(row['insert']) != 2 or
                any(label < 1 or label % 2 == 0 for label in row['remove']+row['insert'])):
            raise ValueError(f'invalid quadratic rule {number}: positive odd pairs required')
        a, b = Counter(row['remove']), Counter(row['insert'])
        ratio_a = Fraction(1)
        ratio_b = Fraction(1)
        for label, power in a.items():
            ratio_a *= Fraction(label, research.step(label))**power
        for label, power in b.items():
            ratio_b *= Fraction(label, research.step(label))**power
        if ratio_a != ratio_b or any(label%3==0 for label in a|b):
            raise ValueError(f'invalid quadratic rule {number}')
        coefficient = row['coefficient']
        if coefficient > 0:
            append_move(f'Q{number}', a, b, coefficient)
        else:
            append_move(f'Q{number}', b, a, -coefficient)
    for name in ('U2','U8','U13'):
        if forced[name] < 0:
            append_move('remove-'+name, units[name], {}, -forced[name])

    delta = {}
    for _, remove, insert in moves:
        subtract_scaled(delta, insert, -1)
        subtract_scaled(delta, remove, 1)
    expected = dict(target)
    subtract_scaled(expected, source, 1)
    if delta != expected:
        raise ValueError('integer witness does not reproduce target-source')

    # The order is deterministic and intentionally simple, not claimed least.
    # Unit insertions are free; among other moves, prefer those already usable.
    state = Counter(source)
    catalyst = Counter()
    pending = list(moves)
    schedule = []
    ordered_moves = []
    while pending:
        def shortage(move):
            return sum(max(0, need-state[label]) for label,need in move[1].items())
        choice = min(range(len(pending)), key=lambda i:(shortage(pending[i]),i))
        kind, remove, insert = pending.pop(choice)
        added = {}
        for label, need in remove.items():
            missing = max(0, need-state[label])
            if missing:
                state[label] += missing
                catalyst[label] += missing
                added[label] = missing
        state.subtract(remove)
        state.update(insert)
        schedule.append({'kind': kind, 'borrowed': [[k,v] for k,v in sorted(added.items())]})
        ordered_moves.append((kind, remove, insert))
    expected_end = Counter(target)+catalyst
    if state != expected_end:
        raise ValueError('catalyst replay endpoint mismatch')

    seed_words,derivations,certified,certify_edge,extra_borrow = (
        validated_borrowing_library())
    newly_borrowable = {}
    changed = True
    while changed:
        changed = False
        for number, row in enumerate(rules):
            for old,new in ((row['remove'],row['insert']),
                            (row['insert'],row['remove'])):
                if set(old) <= certified:
                    for label in new:
                        if label not in certified:
                            certify_edge(label,old,new)
                            newly_borrowable[str(label)] = {'rule': number,
                                'remove': old, 'insert': new}
                            changed = True
    missing = sorted(set(catalyst)-certified-{0})
    if missing:
        return {'value':n, 'status':'unresolved-borrowability',
                'source':[[k,v] for k,v in sorted(source.items()) if v],
                'target':[[k,v] for k,v in sorted(target.items()) if v],
                'forced_net_moves':forced,
                'catalyst':[[k,v] for k,v in sorted(catalyst.items())],
                'catalyst_missing_borrowability':missing,
                'witness_rules':len(rules),
                'oriented_Q_steps':sum(abs(row['coefficient']) for row in rules),
                'vector_replay_exact':True,
                'path_end_replay_exact':True,
                'borrowed_word_value_one':False,
                'full_repair_replay_exact':False}

    unit_cache = {}
    active = set()
    derivation_order = []

    def unit_for(label):
        if label in unit_cache:
            return unit_cache[label].copy()
        if label in active:
            raise ValueError('cyclic borrowing dependency')
        active.add(label)
        if label in seed_words:
            result = seed_words[label].copy()
        else:
            row = derivations[label]
            result = Counter()
            for previous in row['remove']:
                result.update(unit_for(previous))
            for previous in row['remove']:
                if result[previous] <= 0:
                    raise ValueError('borrowed input unavailable')
                result[previous] -= 1
            result.update(row['insert'])
            if result[label] <= 0:
                raise ValueError('derived unit omits requested label')
        active.remove(label)
        unit_cache[label] = result
        derivation_order.append(label)
        return result.copy()

    witness_word = Counter()
    for label, multiplicity in catalyst.items():
        for _ in range(multiplicity):
            witness_word.update(unit_for(label))
    witness_word = Counter({u:c for u,c in witness_word.items() if c})
    if any(witness_word[label] < multiplicity for label,multiplicity in catalyst.items()):
        raise ValueError('borrowed unit word does not dominate catalyst')
    if unit_value(witness_word[0],Counter({u:c for u,c in witness_word.items() if u})) != 1:
        raise ValueError('borrowed word is not a value-one unit')
    legal_state = Counter(source)+witness_word
    for number,(_,remove,insert) in enumerate(ordered_moves):
        if any(legal_state[label] < need for label,need in remove.items()):
            raise ValueError(f'borrowed word does not support move {number}')
        legal_state.subtract(remove)
        legal_state.update(insert)
    if legal_state != Counter(target)+witness_word:
        raise ValueError('legal repair endpoint mismatch')
    return {'value': n, 'status':'legal-repair',
            'source': [[k,v] for k,v in sorted(source.items()) if v],
            'target': [[k,v] for k,v in sorted(target.items()) if v],
            'forced_net_moves': forced,
            'saved_borrowability_file': 'experiments/borrowable_palette_71.json',
            'seed_units': {'U2': {'twos':1,'odds':[[1,1]]},
                           'U8': {'twos':3,'odds':[[k,v] for k,v in sorted(UNIT8.items())]},
                           'U13': {'twos':5,'odds':[[k,v] for k,v in sorted(UNIT13.items())]}},
            'borrow_dag': [{'label': label, **derivations[label]}
                           for label in derivation_order if label not in seed_words],
            'witness_rules': len(rules), 'oriented_Q_steps':
            sum(abs(row['coefficient']) for row in rules),
            'schedule_steps': len(schedule),
            'max_witness_label': max(label for row in rules
                                      for label in row['remove']+row['insert']),
            'catalyst': [[k,v] for k,v in sorted(catalyst.items())],
            'catalyst_missing_borrowability': missing,
            'borrow_unit_factors': sum(witness_word.values()),
            'borrow_unit_support': len(witness_word),
            'borrow_unit': [[k,v] for k,v in sorted(witness_word.items())],
            'borrowability_extra_rule': extra_borrow,
            'newly_borrowable_witnesses': newly_borrowable,
            'schedule': schedule,
            'vector_replay_exact': True,
            'path_end_replay_exact': True,
            'borrowed_word_value_one': True,
            'full_repair_replay_exact': True}


def replay_lattice_71(witness_path):
    return replay_lattice(witness_path,71)


def validated_borrowing_library():
    """Legal unit seeds and individually checked saved quadratic DAG edges."""
    seed_words = {1:Counter({0:1,1:1})}
    for label in UNIT8:
        seed_words[label] = Counter({0:3,**UNIT8})
    for label in UNIT13:
        seed_words.setdefault(label,Counter({0:5,**UNIT13}))
    for word in seed_words.values():
        if unit_value(word[0],Counter({u:v for u,v in word.items() if u})) != 1:
            raise ValueError('invalid palette unit seed')
    certified = set(seed_words)
    derivations = {}

    def add_edge(label, old, new):
        if (len(old) != 2 or len(new) != 2 or label not in new or
                any(u < 1 or u % 2 == 0 or u % 3 == 0 for u in old+new) or
                not set(old) <= certified or
                unit_value(0,Counter(old)) != unit_value(0,Counter(new))):
            raise ValueError(f'invalid saved borrowing edge for {label}')
        for u in new:
            if u not in certified:
                derivations[u] = {'remove':list(old),'insert':list(new)}
        certified.update(new)

    closure = json.loads(Path(__file__).with_name('borrowable_palette_71.json').read_text())
    if set(closure['seed']) != certified:
        raise ValueError('saved closure seed differs from palette')
    for label_text,row in sorted(closure['witness'].items(),
                                 key=lambda item:(item[1]['round'],int(item[0]))):
        add_edge(int(label_text),row['remove'],row['insert'])
    if not set(closure['known_labels']) <= certified:
        raise ValueError('saved closure has uncertified labels')
    replay = json.loads(Path(__file__).with_name('catalytic_palette_71_replay.json').read_text())
    if replay.get('value') != 71 or not replay.get('full_repair_replay_exact'):
        raise ValueError('saved 71 borrowing library has no completed replay')
    for row in replay['borrow_dag']:
        add_edge(row['label'],row['remove'],row['insert'])
    extra = replay['borrowability_extra_rule']
    add_edge(7555,extra['remove'],extra['insert'])
    return seed_words,derivations,certified,add_edge,extra


def borrow_target(target, max_neighbor_calls=20, max_source_label=20000,
                  max_depth=2, max_candidates_per_query=80,
                  max_unit_factors=100000):
    """Bounded target-directed legal borrowing search, independent of any orbit."""
    if target < 1 or target % 2 == 0 or target % 3 == 0:
        raise ValueError('target must be a positive odd 3-free label')
    seed_words,derivations,known,_,_ = validated_borrowing_library()
    initial_known = len(known)
    calls = []
    truncations = set()
    active = set()
    failed = set()

    def derive(label,old,new):
        if not set(old) <= known or label not in new:
            raise ValueError('target-directed borrowing inputs unavailable')
        if unit_value(0,Counter(old)) != unit_value(0,Counter(new)):
            raise ValueError('target-directed quadratic identity invalid')
        for u in new:
            if u not in known:
                derivations[u] = {'remove':list(old),'insert':list(new)}
        known.update(new)

    def visit(label,depth):
        if label in known:
            return True
        if label in active or label in failed:
            return False
        if depth > max_depth:
            truncations.add('max_depth')
            return False
        if label > max_source_label:
            truncations.add('max_source_label')
            return False
        if len(calls) >= max_neighbor_calls:
            truncations.add('max_neighbor_calls')
            return False
        active.add(label)
        rows = research.quadratic_neighbors(label)['nontrivial_exchanges']
        calls.append({'label':label,'complete_neighbors':len(rows)})
        candidates = []
        for row in rows:
            old,new = row['after'],row['before']
            if any(u % 3 == 0 for u in old+new):
                continue
            missing = sorted(set(old)-known)
            if not missing:
                derive(label,old,new)
                active.remove(label)
                return True
            candidates.append((len(missing),max(missing),max(old+new),old,new))
        candidates.sort()
        if len(candidates) > max_candidates_per_query:
            truncations.add('max_candidates_per_query')
        for _,_,_,old,new in candidates[:max_candidates_per_query]:
            if all(visit(u,depth+1) for u in sorted(set(old)-known)):
                derive(label,old,new)
                active.remove(label)
                return True
        active.remove(label)
        failed.add(label)
        return False

    success = visit(target,0)
    result = {'target':target,'status':'borrowable' if success else 'bounded-unresolved',
              'budgets':{'max_neighbor_calls':max_neighbor_calls,
                         'max_source_label':max_source_label,
                         'max_depth':max_depth,
                         'max_candidates_per_query':max_candidates_per_query,
                         'max_unit_factors':max_unit_factors},
              'initial_borrowable_labels':initial_known,
              'complete_neighbor_calls':calls,
              'truncations':sorted(truncations)}
    if not success:
        return result
    cache = {}
    order = []
    building = set()

    def unit_for(label):
        if label in cache:
            return cache[label].copy()
        if label in building:
            raise ValueError('cyclic borrowing DAG')
        building.add(label)
        if label in seed_words:
            word = seed_words[label].copy()
        else:
            edge = derivations[label]
            word = Counter()
            for u in edge['remove']:
                word.update(unit_for(u))
            for u in edge['remove']:
                if word[u] <= 0:
                    raise ValueError('borrowing DAG input unavailable')
                word[u] -= 1
            word.update(edge['insert'])
        building.remove(label)
        if sum(word.values()) > max_unit_factors:
            truncations.add('max_unit_factors')
            raise OverflowError('borrowed unit exceeds factor budget')
        cache[label] = word
        order.append(label)
        return word.copy()

    try:
        word = Counter({u:v for u,v in unit_for(target).items() if v})
    except OverflowError:
        result['status'] = 'unit-budget-truncated'
        result['truncations'] = sorted(truncations)
        return result
    if word[target] < 1 or unit_value(word[0],Counter({u:v for u,v in word.items() if u})) != 1:
        raise ValueError('constructed borrowing word is not a unit containing target')
    used_seed_max = max((u for label in order if label in seed_words
                         for u in seed_words[label] if u > 0),default=0)
    used_edge_max = max((u for label in order if label not in seed_words
                         for u in derivations[label]['remove']+
                                  derivations[label]['insert']),default=0)
    result.update({'unit_factors':sum(word.values()),
                   'unit_max_label':max(word),
                   'construction_max_label':max(used_seed_max,used_edge_max),
                   'unit':[[u,v] for u,v in sorted(word.items())],
                   'borrow_dag':[{'label':u,**derivations[u]}
                                 for u in order if u not in seed_words],
                   'truncations':sorted(truncations)})
    return result


def integer_basis_controls():
    """Tiny exact controls distinguishing integer span from rational span."""
    even = IntegerRelationBasis()
    even.add({7:2},{0:1})
    even_combination, even_remainder = even.express({7:1})
    coprime = IntegerRelationBasis()
    coprime.add({7:2},{0:1})
    coprime.add({7:3},{1:1})
    coprime_combination, coprime_remainder = coprime.express({7:1})
    replay = 2*coprime_combination.get(0,0)+3*coprime_combination.get(1,0)
    return {'two_Z_target_one': {'remainder': even_remainder,
                                 'combination': even_combination},
            'two_three_Z_target_one': {'remainder': coprime_remainder,
                                       'combination': coprime_combination,
                                       'replay': replay}}


def counts(path):
    twos, odds = research.factor_counts(path)
    return twos, odds


def unit_value(twos, odds):
    value = Fraction(2**twos)
    for label, multiplicity in odds.items():
        value *= Fraction(label, research.step(label))**multiplicity
    return value


def palette_ledger(n):
    """Solve the complete rank-4 count system for known n=7 mod 64 paths.

Variables are signed net insertions of U2, U8, U13, and forward cubics.
Positive cubic means {5,55,83} -> {11,13,17}.  Quadratic exchanges
preserve all four recorded counts.  This never assumes arbitrary units.
"""
    data = research.wild_five_repair(n)
    actual_twos, actual_odds = counts(data['actual_path'])
    virtual = data['virtual_prefix'] + data['smaller_path'][1:]
    virtual_twos, virtual_odds = counts(virtual)
    virtual_twos += 2
    virtual_odds.update([7, 7, 11, 17, 55, 65, 83])
    assert actual_twos == data['actual_twos']
    assert virtual_twos == data['virtual_twos']
    assert unit_value(actual_twos, actual_odds) == n
    assert unit_value(virtual_twos, virtual_odds) == n

    dt = actual_twos - virtual_twos
    dk = sum(actual_odds.values()) - sum(virtual_odds.values())
    dm1 = actual_odds[1] - virtual_odds[1]
    dm5 = actual_odds[5] - virtual_odds[5]
    u2 = dm1
    u8 = 5*(dk-u2) - 8*(dt-u2)
    u13 = 5*(dt-u2) - 3*(dk-u2)
    cubic = u13-dm5
    assert (dt, dk, dm1, dm5) == (
        u2+3*u8+5*u13, u2+5*u8+8*u13,
        u2, u13-cubic)
    return {
        'n': n,
        'source': {'twos': virtual_twos,
                   'odd_count': sum(virtual_odds.values()),
                   'm1': virtual_odds[1], 'm5': virtual_odds[5]},
        'target': {'twos': actual_twos,
                   'odd_count': sum(actual_odds.values()),
                   'm1': actual_odds[1], 'm5': actual_odds[5]},
        'delta': {'twos': dt, 'odd_count': dk, 'm1': dm1, 'm5': dm5},
        'forced_net_moves': {'U2': u2, 'U8': u8, 'U13': u13,
                             'cubic_forward': cubic},
        'known_target_steps': len(data['actual_path'])-1,
        'certificate_value': str(unit_value(actual_twos, actual_odds)),
    }


def borrowable_closure(max_label=3077, max_rounds=2, target=71):
    """Bounded quadratic support closure via *complete* pair fibers.

    If a,b each occur in borrowable unit words, take their product, replace
    a,b by any equal-value c,d, and obtain a unit containing c,d.  Returned
    witnesses are actual quadratic edges; exhaustion is only within the
    specified rounds and label ceiling.
    """
    if max_label < 1 or max_rounds < 0:
        raise ValueError('nonnegative rounds and positive label ceiling required')
    seed = {1, *UNIT8, *UNIT13}
    known = {u for u in seed if u <= max_label}
    first_seen = {u: 0 for u in known}
    witness = {}
    evaluated = set()
    pruned_labels = set()
    target_path = research.orbit_to_one(target)
    target_labels = set(u for u in target_path[:-1] if u % 2)
    round_complete = False
    for round_no in range(1, max_rounds+1):
        before = sorted(known)
        added = set()
        for a, b in combinations_with_replacement(before, 2):
            if (a, b) in evaluated:
                continue
            evaluated.add((a, b))
            ratio = Fraction(a, research.step(a))*Fraction(b, research.step(b))
            for c, d in research.two_odd_fiber(ratio)['unordered_odd_pairs']:
                for u in (c,d):
                    if u > max_label:
                        pruned_labels.add(u)
                        continue
                    if u not in known and u not in added:
                        witness[u] = {'round': round_no, 'remove': [a,b],
                                      'insert': [c,d]}
                        first_seen[u] = round_no
                        added.add(u)
        known.update(added)
        if not added:
            round_complete = True
            break
    return {'seed': sorted(seed), 'max_label': max_label,
            'max_rounds': max_rounds, 'known_labels': sorted(known),
            'target': target, 'target_odd_labels': sorted(target_labels),
            'target_labels_missing': sorted(target_labels-known),
            'first_seen': {str(k):v for k,v in sorted(first_seen.items())},
            'witness': {str(k):v for k,v in sorted(witness.items())},
            'pairs_evaluated': len(evaluated),
            'pruned_label_count': len(pruned_labels),
            'round_complete': round_complete}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest='command', required=True)
    ledger = subs.add_parser('ledger')
    ledger.add_argument('n', type=int)
    closure = subs.add_parser('closure')
    closure.add_argument('--max-label', type=int, default=3077)
    closure.add_argument('--max-rounds', type=int, default=2)
    closure.add_argument('--target', type=int, default=71)
    lattice = subs.add_parser('lattice71')
    lattice.add_argument('--max-label', type=int, default=3077)
    lattice.add_argument('--max-aux-label', type=int, default=100000)
    lattice.add_argument('--neighbor-waves', type=int, default=0)
    lattice.add_argument('--wave-width', type=int, default=10)
    lattice.add_argument('--all-pairs', action='store_true')
    lattice.add_argument('--output', type=Path)
    family = subs.add_parser('lattice')
    family.add_argument('n',type=int)
    family.add_argument('--max-label',type=int,default=3077)
    family.add_argument('--max-aux-label',type=int,default=100000)
    family.add_argument('--neighbor-waves',type=int,default=0)
    family.add_argument('--wave-width',type=int,default=10)
    family.add_argument('--max-pairs',type=int,default=30000)
    family.add_argument('--max-neighbor-source-label',type=int,default=5000)
    family.add_argument('--max-rules',type=int,default=5000)
    family.add_argument('--all-pairs',action='store_true')
    family.add_argument('--output',type=Path)
    replay = subs.add_parser('replay71')
    replay.add_argument('witness', type=Path)
    replay.add_argument('--output', type=Path)
    family_replay = subs.add_parser('replay')
    family_replay.add_argument('witness',type=Path)
    family_replay.add_argument('--output',type=Path)
    borrow = subs.add_parser('borrow')
    borrow.add_argument('label',type=int)
    borrow.add_argument('--max-neighbor-calls',type=int,default=20)
    borrow.add_argument('--max-source-label',type=int,default=20000)
    borrow.add_argument('--max-depth',type=int,default=2)
    borrow.add_argument('--max-candidates-per-query',type=int,default=80)
    borrow.add_argument('--max-unit-factors',type=int,default=100000)
    borrow.add_argument('--output',type=Path)
    subs.add_parser('basis-controls')
    subs.add_parser('test')
    args = parser.parse_args()
    if args.command == 'test':
        return subprocess.call(['uv', 'run', '--quiet', '--with', 'pytest',
                                'python3', '-m', 'pytest',
                                str(Path(__file__).with_name('test_catalytic_palette.py')),
                                '-q'])
    if args.command == 'ledger':
        result = palette_ledger(args.n)
    elif args.command == 'lattice71':
        result = relation_lattice_71(args.max_label, args.all_pairs, args.max_aux_label,
                                     args.neighbor_waves, args.wave_width)
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            result = {k:v for k,v in result.items() if k not in ('witness','partial_combination')}
            result['output'] = str(args.output)
    elif args.command == 'lattice':
        result = relation_lattice(args.n,args.max_label,args.all_pairs,
                                  args.max_aux_label,args.neighbor_waves,
                                  args.wave_width,args.max_pairs,
                                  args.max_neighbor_source_label,args.max_rules)
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            result = {k:v for k,v in result.items() if k not in ('witness','partial_combination')}
            result['output'] = str(args.output)
    elif args.command == 'replay71':
        result = replay_lattice_71(args.witness)
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            result = {k:v for k,v in result.items() if k not in ('schedule','newly_borrowable_witnesses')}
            result['output'] = str(args.output)
    elif args.command == 'replay':
        result = replay_lattice(args.witness)
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            result = {k:v for k,v in result.items() if k not in ('schedule','newly_borrowable_witnesses')}
            result['output'] = str(args.output)
    elif args.command == 'borrow':
        result = borrow_target(args.label,args.max_neighbor_calls,
                               args.max_source_label,args.max_depth,
                               args.max_candidates_per_query,args.max_unit_factors)
        if args.output:
            args.output.write_text(json.dumps(result,indent=2)+'\n')
            result = {k:v for k,v in result.items() if k not in ('unit','borrow_dag')}
            result['output'] = str(args.output)
    elif args.command == 'basis-controls':
        result = integer_basis_controls()
    else:
        result = borrowable_closure(args.max_label, args.max_rounds, args.target)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
