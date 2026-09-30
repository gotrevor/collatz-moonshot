#!/usr/bin/env -S uv run --quiet --with scipy python3
"""Exact controls for three Collatz research proposals, not a convergence test."""
from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import prod, isqrt
from pathlib import Path
import argparse
import json
import subprocess
import sys


def step(n):
    return (3*n+1)//2 if n%2 else n//2


def map_step(n, multiplier=3, offset=1):
    """Shortcut qx+c map.  (3,-1) on positive n is 3x+1 on -n, conjugated."""
    if multiplier < 3 or multiplier%2 == 0 or offset not in (-1,1):
        raise ValueError('positive odd multiplier >=3, offset +/-1 required')
    return (multiplier*n+offset)//2 if n%2 else n//2


def certificate(twos, odd_sources, multiplier=3, offset=1):
    """Check both commutative value and exact backward-path realization.

    A factor 2 is usable at any positive state.  A factor u/T(u) is usable
    only at T(u), where its backward edge leads to u.  Every factor is used.
    """
    if twos < 0 or any(u < 1 or u%2 == 0 for u in odd_sources):
        raise ValueError('need nonnegative twos and positive odd sources')
    def step(u):
        return map_step(u,multiplier,offset)
    value=Fraction(2**twos)*prod((Fraction(u,step(u)) for u in odd_sources),start=Fraction(1))
    counts=Counter(odd_sources)
    sources=tuple(sorted(counts))

    @lru_cache(None)
    def visit(current, left_twos, remaining):
        if not left_twos and not any(remaining):
            return (current,)
        if left_twos:
            tail=visit(2*current,left_twos-1,remaining)
            if tail is not None:
                return (current,)+tail
        for i,u in enumerate(sources):
            if remaining[i] and step(u)==current:
                next_counts=list(remaining)
                next_counts[i]-=1
                tail=visit(u,left_twos,tuple(next_counts))
                if tail is not None:
                    return (current,)+tail
        return None

    path=visit(1,twos,tuple(counts[u] for u in sources))
    return {'value':str(value),'realizable':path is not None,
            'backward_path':list(path) if path is not None else None,
            'states_examined':visit.cache_info().currsize}


def pair_energy(word, multiplier=3, offset=1):
    """Vandermonde transport on the exact rational cycle of a parity word."""
    if not word or any(c not in '01' for c in word):
        raise ValueError('nonempty binary word required')
    if multiplier < 3 or multiplier%2 == 0 or offset not in (-1,1):
        raise ValueError('positive odd multiplier >=3, offset +/-1 required')
    numer=0
    for i,c in enumerate(word):
        if c=='1':
            numer=multiplier*numer+offset*2**i
    denominator=2**len(word)-multiplier**word.count('1')
    if denominator==0:
        raise ValueError('zero cycle denominator')
    start=Fraction(numer,denominator)
    states=[]
    n=start
    for c in word:
        if n.denominator%2==0 or n.numerator%2!=int(c):
            raise AssertionError('rational parity mismatch')
        states.append(n)
        n=(multiplier*n+offset)/2 if c=='1' else n/2
    if n!=start:
        raise AssertionError('cycle did not close')
    if len(set(states))!=len(states):
        raise ValueError('primitive cycle required: repeated state')
    evens=[x for x,c in zip(states,word) if c=='0']
    odds=[x for x,c in zip(states,word) if c=='1']
    ratio=prod((abs((multiplier*o+offset-e)/(o-e)) for e in evens for o in odds),start=Fraction(1))
    m,k=len(states),len(odds)
    expected=Fraction(2**(m*(m-1)//2),multiplier**(k*(k-1)//2))
    gaps=[abs(x-y) for x,y in combinations(states,2)]
    return {'word':word,'states':list(map(str,states)),
            'mixed_ratio':str(ratio),'required_ratio':str(expected),
            'identity_holds':ratio==expected,
            'integral':all(x.denominator==1 for x in states),
            'minimum_gap':str(min(gaps)) if gaps else None}


def dyadic_ray_coefficient(n, base):
    if n < base or n%base:
        return 0
    q=n//base
    return int(q & (q-1) == 0)


def signed_fixed(odd_source, cutoff):
    """The known signed fixed series D_(3u+1)-D_u, using exact coefficients.

    Values beyond cutoff are evaluated by formula, not discarded.  Thus the
    residual check is not corrupted by a truncation boundary.
    """
    if odd_source < 1 or odd_source%2==0 or cutoff < 1:
        raise ValueError('positive odd source and positive cutoff required')
    def coefficient(n):
        return dyadic_ray_coefficient(n,3*odd_source+1)-dyadic_ray_coefficient(n,odd_source)
    negative=[]
    positive=[]
    residuals=[]
    for n in range(1,cutoff+1):
        a=coefficient(n)
        if a<0: negative.append(n)
        if a>0: positive.append(n)
        pushed=coefficient(2*n)
        if n%3==2:
            pushed+=coefficient((2*n-1)//3)
        if pushed!=a:
            residuals.append([n,pushed-a])
    return {'odd_source':odd_source,'cutoff':cutoff,'positive':positive,
            'negative':negative,'residuals':residuals}


def multiplicative_fixed(cutoff):
    """Positive sparse fixed series for G(n)=n/2 even, 3n odd.

    This is a control for arguments that forget the actual +1 map.
    The support is {2^k:k>=0} union {3^j:j>=1}.
    """
    if cutoff < 1:
        raise ValueError('positive cutoff required')
    def coefficient(n):
        if dyadic_ray_coefficient(n,1):
            return 1
        if n < 3:
            return 0
        while n%3==0:
            n//=3
        return int(n==1)
    support=[]
    residuals=[]
    for n in range(1,cutoff+1):
        a=coefficient(n)
        if a:
            support.append(n)
        pushed=coefficient(2*n)
        if n%6==3:
            pushed+=coefficient(n//3)
        if pushed!=a:
            residuals.append([n,pushed-a])
    return {'cutoff':cutoff,'support':support,'residuals':residuals}


def approximate_fixed(depth, cutoff):
    """Positive approximate fixed vectors for the actual Collatz operator.

    Infinite dyadic tail is evaluated exactly; it is never truncated when
    checking the coefficient equation.  Norm is sum |a_n|/n.
    """
    if depth < 2 or cutoff < 1:
        raise ValueError('depth >=2 and positive cutoff required')
    orbit=[3**j*2**(depth-j)-1 for j in range(depth+1)]
    base=orbit[0]
    forward=set(orbit[1:-1])
    def coefficient(n):
        return dyadic_ray_coefficient(n,base)+int(n in forward)
    residuals=[]
    for n in range(1,cutoff+1):
        pushed=coefficient(2*n)
        if n%3==2:
            pushed+=coefficient((2*n-1)//3)
        error=pushed-coefficient(n)
        if error:
            residuals.append([n,error])
    mass=Fraction(2,base)+sum((Fraction(1,n) for n in forward),start=Fraction(0))
    error_mass=Fraction(1,orbit[-1])
    return {'depth':depth,'orbit':orbit,'endpoint':orbit[-1],
            'weighted_mass':str(mass),'error_mass':str(error_mass),
            'relative_error':str(error_mass/mass),
            'upper_bound':str(Fraction(2,3)**depth),
            'cutoff':cutoff,'residuals':residuals}


def nearly_positive_fixed(depth, cutoff):
    """Exact signed fixed vector whose negative mass is exponentially small.

    H_K = F_K - D_(2*(3^K-1)), K positive even.  The supports are disjoint:
    the positive dyadic base is divisible by 3, the negative one is not,
    and the remaining positive points are odd while the negative ray is even.
    """
    if depth < 2 or depth%2 or cutoff < 1:
        raise ValueError('positive even depth >=2 and positive cutoff required')
    data=approximate_fixed(depth,1)
    base=data['orbit'][0]
    endpoint=data['endpoint']
    forward=set(data['orbit'][1:-1])
    def coefficient(n):
        return dyadic_ray_coefficient(n,base)+int(n in forward)-dyadic_ray_coefficient(n,2*endpoint)
    positive=[]
    negative=[]
    residuals=[]
    for n in range(1,cutoff+1):
        a=coefficient(n)
        if a>0: positive.append(n)
        if a<0: negative.append(n)
        pushed=coefficient(2*n)
        if n%3==2:
            pushed+=coefficient((2*n-1)//3)
        if pushed!=a:
            residuals.append([n,pushed-a])
    positive_mass=Fraction(data['weighted_mass'])
    negative_mass=Fraction(1,endpoint)
    return {'depth':depth,'cutoff':cutoff,'positive':positive,'negative':negative,
            'positive_mass':str(positive_mass),'negative_mass':str(negative_mass),
            'negative_to_positive':str(negative_mass/positive_mass),
            'upper_bound':str(Fraction(2,3)**depth),'residuals':residuals}


def gap_control(parameter):
    if parameter < 1:
        raise ValueError('positive integer parameter required')
    states=[Fraction(63,5),Fraction(126,5),Fraction(126+125*parameter,5)]
    differences=[abs(x-y) for x,y in combinations(states,2)]
    return {'parameter':parameter,'states':list(map(str,states)),
            'minimum_gap':str(min(differences)),
            'vandermonde':str(prod(differences)),
            'has_halving_edge':states[1]/2==states[0],
            'integral_states':all(x.denominator==1 for x in states),
            'closed_under_collatz':all(((3*x+1)/2 if x.numerator%2 else x/2) in states for x in states)}


def odd_boundary(sources):
    boundary=Counter()
    for u in sources:
        boundary[u]+=1
        boundary[step(u)]-=1
    return {u:c for u,c in sorted(boundary.items()) if c}


def two_edge_repair(parameter):
    """A parametric neutral exchange, discovered by solving factor cancellation.

    r_(23t) r_((483t+7)/2) = r_(35t) r_((105t+1)/2), t=1 mod4.
    The right pair is the connected path 35t -> (105t+1)/2 -> (315t+5)/4.
    """
    t=parameter
    if t < 1 or t%4!=1:
        raise ValueError('positive parameter=1 mod4 required')
    disconnected=[23*t,(483*t+7)//2]
    connected=[35*t,(105*t+1)//2]
    before=odd_boundary(disconnected)
    after=odd_boundary(connected)
    before_value=prod((Fraction(u,step(u)) for u in disconnected),start=Fraction(1))
    after_value=prod((Fraction(u,step(u)) for u in connected),start=Fraction(1))
    assert before_value==after_value
    assert step(connected[0])==connected[1]
    result={'parameter':t,'disconnected_sources':disconnected,
            'connected_path':connected+[step(connected[-1])],
            'value':str(before_value),'before_boundary':before,'after_boundary':after,
            'before_boundary_l1':sum(map(abs,before.values())),
            'after_boundary_l1':sum(map(abs,after.values()))}
    if t==1:
        # Background even path 16 -> 8 -> 4 -> 2 -> 1; scalar target 7.
        def defect(boundary):
            d=Counter(boundary)
            d[16]+=1
            d[7]-=1
            return {u:c for u,c in sorted(d.items()) if c}
        db,da=defect(before),defect(after)
        result['certificate_seven']={
            'before':certificate(4,disconnected),'after':certificate(4,connected),
            'before_defect':db,'after_defect':da,
            'before_defect_l1':sum(map(abs,db.values())),
            'after_defect_l1':sum(map(abs,da.values()))}
    return result


def positive_divisors_of_product(parts):
    """Factor the small parts separately, then enumerate product divisors."""
    powers=Counter()
    for part in parts:
        if part<1:
            raise ValueError('positive factors required')
        divisor=2
        while divisor*divisor<=part:
            while part%divisor==0:
                powers[divisor]+=1
                part//=divisor
            divisor=3 if divisor==2 else divisor+2
        if part>1:
            powers[part]+=1
    divisors=[1]
    for prime,exponent in powers.items():
        divisors=[d*prime**e for d in divisors for e in range(exponent+1)]
    return divisors


def two_odd_fiber(value):
    """All positive odd pairs with r_c*r_d=value, with no label cutoff.

    With value=A/B and D=4B-9A, factor
    (D*c-3A)(D*d-3A)=4AB.  Both factors must be positive.
    """
    ratio=Fraction(value)
    if not 0 < ratio < Fraction(4,9):
        raise ValueError('ratio must lie strictly between 0 and 4/9')
    A,B=ratio.numerator,ratio.denominator
    D=4*B-9*A
    total=4*A*B
    divisors=positive_divisors_of_product([4,A,B])
    pairs=[]
    for left in sorted(d for d in divisors if d*d<=total):
        right=total//left
        if (left+3*A)%D or (right+3*A)%D:
            continue
        c,d=(left+3*A)//D,(right+3*A)//D
        if c%2 and d%2:
            pairs.append([c,d])
    result={'ratio':str(ratio),'D':D,'factor_product':total,'unordered_odd_pairs':pairs}
    if ratio==Fraction(7,16):
        rows=[]
        for pair in pairs:
            boundary=Counter(odd_boundary(pair))
            boundary[16]+=1
            boundary[7]-=1
            rows.append({'sources':pair,'defect_l1':sum(map(abs,boundary.values())),
                         'realizable':certificate(4,pair)['realizable']})
        result['certificate_seven_fiber']=rows
    return result


def pair_discriminant(word):
    data=pair_energy(word)
    states=list(map(Fraction,data['states']))
    vandermonde=prod((abs(x-y) for x,y in combinations(states,2)),start=Fraction(1))
    return {**data,'vandermonde':str(vandermonde),
            'discriminant_integral':vandermonde.denominator==1,
            'vandermonde_denominator':vandermonde.denominator,
            'all_differences_integral':all((x-y).denominator==1 for x,y in combinations(states,2))}


def discriminant_scan(depth):
    if depth < 2 or depth > 18:
        raise ValueError('scan depth must be between 2 and 18')
    examined=0
    counterexamples=[]
    for length in range(2,depth+1):
        for bits in product('01',repeat=length):
            word=''.join(bits)
            if '1' not in word or 2**length <= 3**word.count('1'):
                continue
            rotations=[word[j:]+word[:j] for j in range(length)]
            if word!=min(rotations) or len(set(rotations))!=length:
                continue
            data=pair_discriminant(word)
            examined+=1
            if not data['integral'] and data['discriminant_integral']:
                counterexamples.append(data)
    return {'depth':depth,'positive_primitive_cycles_examined':examined,
            'nonintegral_cycles_with_integral_discriminant':counterexamples}


def orbit_to_one(n, cap=10000):
    path=[]
    seen=set()
    while n!=1:
        if n in seen or len(path)>=cap:
            raise ValueError('orbit hit a cycle or step cap before 1')
        seen.add(n)
        path.append(n)
        n=step(n)
    return path+[1]


def factor_counts(path):
    twos=sum(n%2==0 for n in path[:-1])
    odds=Counter(n for n in path[:-1] if n%2)
    return twos,odds


def wild_five_repair(n):
    """Audit the actual 5-multiplier certificate on n=7 mod 64.

    Paper certificate: 1/5 = 2^2 r_7^2 r_11 r_17 r_55 r_65 r_83.
    Virtual six-step descent: 5n -> (45n+5)/64 < n.
    All orbit traversals are capped; no convergence claim is inferred.
    """
    if n < 7 or n%64!=7:
        raise ValueError('positive n=7 mod64 required')
    m=(45*n+5)//64
    virtual=[5*n]
    for _ in range(6):
        virtual.append(step(virtual[-1]))
    assert virtual[-1]==m
    actual=orbit_to_one(n)
    smaller=orbit_to_one(m)
    atwos,aodds=factor_counts(actual)
    vtwos,vodds=factor_counts(virtual+smaller[1:])
    vtwos+=2
    vodds.update([7,7,11,17,55,65,83])
    avalue=Fraction(2**atwos)*prod((Fraction(u,step(u))**c for u,c in aodds.items()),start=Fraction(1))
    vvalue=Fraction(2**vtwos)*prod((Fraction(u,step(u))**c for u,c in vodds.items()),start=Fraction(1))
    assert avalue==vvalue==n
    smaller_indices={u:i for i,u in enumerate(smaller)}
    a=next(i for i,u in enumerate(actual) if u in smaller_indices)
    b=smaller_indices[actual[a]]
    common=aodds&vodds
    extra_actual=aodds-common
    extra_virtual=vodds-common
    cancelled_twos=min(atwos,vtwos)
    return {'n':n,'smaller_endpoint':m,'virtual_prefix':virtual,
            'actual_path':actual,'smaller_path':smaller,
            'certificate_value':str(vvalue),
            'actual_factors':len(actual)-1,
            'virtual_factors':vtwos+sum(vodds.values()),
            'actual_twos':atwos,'virtual_twos':vtwos,
            'meeting':actual[a],'meeting_steps':[a,b],
            'exchange':{
                'remove_twos':vtwos-cancelled_twos,
                'add_twos':atwos-cancelled_twos,
                'remove_odds':sorted(extra_virtual.elements()),
                'add_odds':sorted(extra_actual.elements()),
            }}



def odd_factor_fiber(value, count, least=1):
    """Exact finite enumeration, sorted odd labels, no height cutoff.

    r_u is strictly increasing towards 2/3.  If u is the smallest of k
    remaining labels, r_u**k <= value < (2/3)**k.  This gives a finite
    upper bound by exact binary search.  The last two factors use the
    divisor identity, and the last factor is solved directly.
    """
    ratio=Fraction(value)
    if count < 1 or count > 5 or least < 1 or least%2==0:
        raise ValueError('count in 1..5 and positive odd least label required')
    def solve(q,k,lo):
        if not 0 < q < Fraction(2,3)**k or Fraction(lo,step(lo))**k>q:
            return
        if k==1:
            u=q/(2-3*q)
            if u.denominator==1 and u.numerator>=lo and u.numerator%2:
                yield [u.numerator]
            return
        if k==2:
            for pair in two_odd_fiber(q)['unordered_odd_pairs']:
                if pair[0]>=lo:
                    yield pair
            return
        high=max(lo,3)
        while Fraction(2*high,3*high+1)**k<=q:
            high*=2
        low=lo
        while low+1<high:
            mid=(low+high)//2
            if Fraction(2*mid,3*mid+1)**k<=q:
                low=mid
            else:
                high=mid
        for u in range(lo,low+1,2):
            for tail in solve(q/Fraction(u,step(u)),k-1,u):
                yield [u]+tail
    solutions=list(solve(ratio,count,least))
    return {'ratio':str(ratio),'count':count,'least':least,
            'unordered_odd_tuples':solutions,'height_cutoff':None}


def unit_parity():
    """Arithmetic reduction proving odd unit length is at least thirteen.

    Delete copies of 2*r_1=1.  A unit has no 3-divisible label, so every
    remaining odd label is >=5.  The interval 5/8 <= r_u < 2/3 leaves
    exactly (twos,odds)=(2,3) below length 13 with odd length.  Its least
    label must be 5; the residual two-factor fiber of 2/5 is empty.
    """
    candidates=[]
    for twos in range(13):
        for odds in range(1,13-twos):
            if (twos+odds)%2 and Fraction(2**twos)*Fraction(5,8)**odds<=1<                    Fraction(2**twos)*Fraction(2,3)**odds:
                candidates.append([twos,odds])
    sources=[5,7,7,11,17,55,65,83]
    short_candidates=[[t,k] for t in range(8) for k in range(1,8-t)
                      if Fraction(2**t)*Fraction(5,8)**k<=1<
                         Fraction(2**t)*Fraction(2,3)**k]
    return {'odd_length_candidates_below_thirteen':candidates,
            'reduced_unit_candidates_below_eight':short_candidates,
            'candidate_triple_fiber':odd_factor_fiber('1/4',3,5),
            'unit_twos':5,'unit_odd_sources':sources,'unit_length':13,
            'unit_value':certificate(5,sources)['value']}


def dyadic_pair_ledger(word):
    """Compare exact rational v2 gaps with cyclic parity-prefix collisions."""
    data=pair_energy(word)
    states=list(map(Fraction,data['states']))
    m=len(word)
    def v2(x):
        q=abs(x)
        a,b=q.numerator,q.denominator
        return (a & -a).bit_length()-(b & -b).bit_length()
    rows=[]
    for i,j in combinations(range(m),2):
        common=next(k for k in range(m) if word[(i+k)%m]!=word[(j+k)%m])
        rows.append({'indices':[i,j],'gap_v2':v2(states[i]-states[j]),
                     'common_prefix':common})
    collisions=[]
    for length in range(1,m):
        counts=Counter(''.join(word[(i+k)%m] for k in range(length)) for i in range(m))
        pairs=sum(c*(c-1)//2 for c in counts.values())
        if pairs:
            collisions.append([length,pairs])
    return {'word':word,'states':data['states'],'integral':data['integral'],
            'pairs':rows,'prefix_collision_counts':collisions,
            'vandermonde_v2':sum(row['gap_v2'] for row in rows),
            'prefix_collision_sum':sum(c for _,c in collisions)}



def quadratic_path(sources, target, max_label, max_states):
    """Bounded search using complete two-factor fibers at each visited pair.

    A returned path is exact; failure is explicitly bounded and proves no
    global disconnection.  No actual Collatz trajectory is used by the search.
    """
    start=tuple(sorted(sources))
    end=tuple(sorted(target))
    if len(start)!=len(end) or not start or any(u<1 or u%2==0 for u in start+end):
        raise ValueError('equal nonzero numbers of positive odd factors required')
    def value(state):
        return prod((Fraction(u,step(u)) for u in state),start=Fraction(1))
    if value(start)!=value(end):
        raise ValueError('source and target must have equal scalar value')
    if max_label<max(start+end) or max_states<1:
        raise ValueError('bounds must contain the endpoints')
    @lru_cache(None)
    def alternatives(a,b):
        return two_odd_fiber(Fraction(a,step(a))*Fraction(b,step(b)))['unordered_odd_pairs']
    parent={start:None}
    queue=deque([start])
    found=start==end
    height_pruned=0
    largest_proposed=max(start)
    while queue and not found and len(parent)<max_states:
        state=queue.popleft()
        for i,j in combinations(range(len(state)),2):
            for a,b in alternatives(state[i],state[j]):
                largest_proposed=max(largest_proposed,b)
                if b>max_label:
                    height_pruned+=1
                    continue
                nxt=tuple(sorted([u for k,u in enumerate(state) if k not in (i,j)]+[a,b]))
                if nxt in parent:
                    continue
                parent[nxt]=state
                queue.append(nxt)
                if nxt==end:
                    found=True
                    break
                if len(parent)>=max_states:
                    break
            if found or len(parent)>=max_states:
                break
    path=[]
    if found:
        node=end
        while node is not None:
            path.append(list(node))
            node=parent[node]
        path.reverse()
    return {'value':str(value(start)),'path':path or None,
            'max_label':max_label,'max_states':max_states,
            'states_seen':len(parent),'bounded_graph_exhausted':not queue and not found,
            'height_pruned':height_pruned,'largest_proposed_label':largest_proposed,
            'visited_states':list(map(list,sorted(parent))) if len(parent)<=50 else None}


def catalytic_seven():
    # 2^3 r19 r25 r29 r55 r83=1, by the visible cancellations
    # (19/29)(25/38)(29/44)(55/83)(83/125)=1/8.
    unit8=[19,25,29,55,83]
    unit13=[5,7,7,11,17,55,65,83]
    before=[7,35,53,65]
    after=[13,19,25,29]
    def scalar(labels):
        return prod((Fraction(u,step(u)) for u in labels),start=Fraction(1))
    labels=Counter([35,53])
    stages=[{'twos':4,'sources':sorted(labels.elements())}]
    labels.update(unit13)
    stages.append({'twos':9,'sources':sorted(labels.elements())})
    labels.subtract([35,53]); labels.update([25,133])
    stages.append({'twos':9,'sources':sorted(labels.elements())})
    labels.subtract([7,65,133]); labels.update([13,19,29])
    stages.append({'twos':9,'sources':sorted(labels.elements())})
    labels.subtract(unit8)
    assert all(v>=0 for v in labels.values())
    stages.append({'twos':6,'sources':sorted(labels.elements())})
    for row in stages:
        row['value']=str(Fraction(2**row['twos'])*scalar(row['sources']))
    return {'stages':stages,'unit8':{'twos':3,'sources':unit8,'value':str(8*scalar(unit8))},
            'unit13':{'twos':5,'sources':unit13,'value':str(32*scalar(unit13))},
            'count_lattice_determinant':3*8-5*5,
            'exchange':{'before':before,'after':after,'before_value':str(scalar(before)),
                        'after_value':str(scalar(after))},
            'original':certificate(4,[35,53]),
            'repaired':certificate(6,[7,11,17,13,5])}


def anchored_cut(n, cutoff):
    """Attain the exact 1/peak defect constant for a checked convergent start.

    This is a witness/control, not an algorithm for proving an unknown orbit
    bounded.  The infinite dyadic ray is evaluated at every queried preimage.
    """
    if n<3 or cutoff<1:
        raise ValueError('start >=3 and positive cutoff required')
    path=orbit_to_one(n)
    peak=max(path[1:])
    end=path.index(peak,1)
    prefix=set(path[1:end])
    future=set(path[1:])|{1,2}
    def coefficient(u):
        return dyadic_ray_coefficient(u,n)+int(u in prefix)
    def residual(u):
        pushed=coefficient(2*u)
        if u%3==2:
            pushed+=coefficient((2*u-1)//3)
        return pushed-coefficient(u)
    rows=[[u,residual(u)] for u in range(1,cutoff+1) if residual(u)]
    return {'start':n,'peak_future':peak,'prefix_to_peak':path[:end+1],
            'anchor_coefficient':coefficient(n),
            'cycle_coefficients':[coefficient(1),coefficient(2)],
            'sharp_defect_norm':str(Fraction(1,peak)),
            'forward_cut_residual_sum':sum(residual(u) for u in future),
            'cutoff':cutoff,'residuals':rows}



def quadratic_neighbors(a):
    """All nontrivial pair exchanges involving r_a, with no label cutoff.

    Sort c<=d; then c<2a+1.  For alpha=3(a-c), beta=a(3c+1),
    gamma=c(3a+1), equality factors as
        (gamma-alpha*b)*(beta+alpha*d)=beta*gamma.
    Both factors are positive: gamma-alpha*b=beta*b/d.
    Divisors replace the old long scan over b or d.  Factor the four
    small terms a,c,3c+1,3a+1 separately, not their large product.
    """
    if a<1 or a%2==0:
        raise ValueError('positive odd label required')
    rows=set()
    for c in range(1,2*a+1,2):
        if c==a:
            continue
        alpha=3*(a-c)
        beta=a*(3*c+1)
        gamma=c*(3*a+1)
        total=beta*gamma
        for x in positive_divisors_of_product([a,c,3*c+1,3*a+1]):
            y=total//x
            if (gamma-x)%alpha or (y-beta)%alpha:
                continue
            b=(gamma-x)//alpha
            d=(y-beta)//alpha
            if b<1 or d<c or b%2==0 or d%2==0:
                continue
            old=tuple(sorted([a,b]));new=(c,d)
            if old!=new:
                rows.add((old,new))
    return {'label':a,'nontrivial_exchanges':[{'before':list(x),'after':list(y)} for x,y in sorted(rows)],
            'frozen':not rows,'height_cutoff':None}



def unit_assisted_seven():
    """Repair using eight quadratic moves and the two fixed unit words."""
    unit8=[19,25,29,55,83]
    unit13=[5,7,7,11,17,55,65,83]
    moves=[([35,53],[25,133]),([65,133],[53,247]),
           ([17,53],[13,901]),([247,901],[221,1577]),
           ([11,221],[13,55]),([55,1577],[95,121]),
           ([13,95],[19,29]),([7,121],[11,17])]
    labels=Counter([35,53]+unit13)
    stages=[sorted(labels.elements())]
    def value(pair):
        return prod((Fraction(u,step(u)) for u in pair),start=Fraction(1))
    for old,new in moves:
        assert not (Counter(old)-labels)
        assert value(old)==value(new)
        labels.subtract(old);labels.update(new)
        stages.append(sorted(labels.elements()))
    assert not (Counter(unit8)-labels)
    labels.subtract(unit8)
    return {'original_twos':4,'insert_unit':{'twos':5,'sources':unit13},
            'moves':[{'remove':old,'add':new,'value':str(value(old))} for old,new in moves],
            'stages':stages,'stage_values':[str(512*value(row)) for row in stages],
            'remove_unit':{'twos':3,'sources':unit8},
            'final_twos':6,'final_sources':sorted(labels.elements()),
            'final_certificate':certificate(6,list(labels.elements()))}


def palette_obstruction():
    """Index preserved by quadratic moves and the three initial unit words.

    Frozen multiplicities m1,m5 give I=5*twos-3*odd_count-m5-2*m1.
    The index is not a scalar invariant: the two certificates of 71 differ.
    The cubic r5*r55*r83=r11*r13*r17 breaks it by one.
    """
    def index(t,labels):
        return 5*t-3*len(labels)-labels.count(5)-2*labels.count(1)
    unit8=[19,25,29,55,83]
    unit13=[5,7,7,11,17,55,65,83]
    new_unit13=[7,7,11,11,13,17,17,65]
    virtual=[25,19,29,11,17,13,5,355,533,7,7,11,17,55,65,83]
    actual=orbit_to_one(71)
    twos,odds=factor_counts(actual)
    actual_odds=list(odds.elements())
    left=[5,55,83];right=[11,13,17]
    def value(labels):
        return prod((Fraction(u,step(u)) for u in labels),start=Fraction(1))
    return {'unit_indices':{'trivial':index(1,[1]),'eight':index(3,unit8),
                            'thirteen':index(5,unit13)},
            'seventy_one':{'virtual_index':index(16,virtual),'actual_index':index(twos,actual_odds),
                          'actual_twos':twos,'actual_odds':actual_odds},
            'essential_cubic':{'left':left,'right':right,'left_value':str(value(left)),
                               'right_value':str(value(right)),
                               'index_change':index(0,right)-index(0,left)},
            'new_unit':{'twos':5,'sources':new_unit13,'value':str(32*value(new_unit13)),
                        'index':index(5,new_unit13)}}


def orbit_fate(n, multiplier=3, offset=1, cap=100000):
    """Where the positive orbit of n goes: 1, another cycle, or past the cap."""
    seen={}
    path=[]
    x=n
    while x not in seen and len(path) < cap:
        if x == 1:
            return {'n':n,'fate':'reaches_one','steps':len(path),
                    'orbit_min':min(path+[1])}
        seen[x]=len(path)
        path.append(x)
        x=map_step(x,multiplier,offset)
    if x in seen:
        cycle=path[seen[x]:]
        return {'n':n,'fate':'cycle','cycle':sorted(cycle),'cycle_min':min(cycle),
                'orbit_min':min(path),'steps_to_cycle':seen[x]}
    return {'n':n,'fate':'cap','steps':cap,'orbit_min':min(path)}


def small_primes(bound):
    return [p for p in range(3,bound+1) if all(p%d for d in range(2,isqrt(p)+1))]


def smooth_exponents(x, primes):
    """Exponents of 2 and the given odd primes, or None if x has another prime."""
    exps={}
    for p in [2]+primes:
        while x%p == 0:
            exps[p]=exps.get(p,0)+1
            x//=p
    return exps if x == 1 else None


def supply(n, multiplier=3, offset=1, max_label=20000, prime_bound=60):
    """Fewest-label semigroup word 2^e * prod u/T(u) with exact value n.

    Integer program over odd labels u <= max_label with u and T(u) both
    prime_bound-smooth.  Infeasible means only 'none within these bounds'.
    The returned word is re-evaluated exactly; realizability as a backward
    path from 1 and the actual orbit fate of n are reported beside it.
    """
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    primes=small_primes(prime_bound)
    coords=[2]+primes
    index={p:i for i,p in enumerate(coords)}
    target=smooth_exponents(n,primes)
    if n < 1 or target is None:
        raise ValueError('n must be a positive prime_bound-smooth integer')
    columns=[np.eye(len(coords))[0]]
    labels=[2]
    for u in range(1,max_label+1,2):
        image=map_step(u,multiplier,offset)
        top,bottom=smooth_exponents(u,primes),smooth_exponents(image,primes)
        if top is None or bottom is None:
            continue
        column=np.zeros(len(coords))
        for p,e in top.items():
            column[index[p]]+=e
        for p,e in bottom.items():
            column[index[p]]-=e
        if column.any():
            columns.append(column)
            labels.append(u)
    rhs=np.zeros(len(coords))
    for p,e in target.items():
        rhs[index[p]]=e
    cost=np.ones(len(labels))
    cost[0]=0
    solved=milp(cost,constraints=LinearConstraint(np.array(columns).T,rhs,rhs),
                integrality=np.ones(len(labels)),bounds=Bounds(0,256))
    base={'n':n,'multiplier':multiplier,'offset':offset,'max_label':max_label,
          'prime_bound':prime_bound,'candidate_labels':len(labels)-1,
          'fate':orbit_fate(n,multiplier,offset)}
    if not solved.success:
        return {**base,'found':False,'solver':solved.message}
    counts=[int(round(x)) for x in solved.x]
    twos=counts[0]
    sources=sorted(u for u,c in zip(labels[1:],counts[1:]) for _ in range(c))
    checked=certificate(twos,sources,multiplier,offset)
    if Fraction(checked['value']) != n:
        raise AssertionError('solver word does not evaluate to n')
    components={u:orbit_fate(u,multiplier,offset) for u in sorted(set(sources))}
    return {**base,'found':True,'twos':twos,'odd_sources':sources,
            'value':checked['value'],'realizable':checked['realizable'],
            'label_fates':{u:(f['cycle_min'] if f['fate'] == 'cycle' else f['fate'])
                           for u,f in components.items()}}


def exchanges(multiplier=3, offset=1, max_label=300):
    """All 2-for-2 scalar exchanges T-ratio(a)T-ratio(b)=T-ratio(c)T-ratio(d)."""
    classes={}
    for a in range(1,max_label,2):
        for b in range(a,max_label,2):
            value=(Fraction(a,map_step(a,multiplier,offset))*
                   Fraction(b,map_step(b,multiplier,offset)))
            classes.setdefault(value,[]).append([a,b])
    found=[pairs for pairs in classes.values() if len(pairs) > 1]
    return {'multiplier':multiplier,'offset':offset,'max_label':max_label,
            'exchange_classes':len(found),'first':found[:5],'all':found}


def cubic_twin(b):
    """The variable cubic of CubicPeel at a=-b, read as a 3x-1 identity.

    r_(-x)=2x/(3x-1), so every rational-function identity among 3x+1 ratios
    with affine labels holds among 3x-1 ratios with the labels negated.
    """
    a=-b
    left=[5*a-2,Fraction(3*a-1,64),Fraction(5*(2*a-7),93)]
    right=[a,Fraction(3*a+1,58),Fraction(2*a-7,21)]
    left,right=[-x for x in left],[-x for x in right]
    def value(labels):
        return prod((Fraction(2*x)/(3*x-1) for x in labels),start=Fraction(1))
    legal=all(x.denominator == 1 and x > 0 and x.numerator%2 == 1 and x.numerator%3
              for x in left+right)
    return {'b':b,'left':[str(x) for x in left],'right':[str(x) for x in right],
            'left_value':str(value(left)),'right_value':str(value(right)),
            'equal':value(left) == value(right),'positive_odd_three_free':legal}


def map_control(max_label=20000):
    """Known-negative controls for the certificate-repair toolkit.

    3x-1 (= 3x+1 on negatives) and 5x+1 have positive non-convergent starts.
    If supply and exchanges exist there too, no map-agnostic repair rank
    can close; it must fail at the cycle starts below.
    """
    conjugate=all(Fraction(-2*u,-3*u+1) == Fraction(2*u,3*u-1) for u in range(1,1000,2))
    units={'plus_U8':(3,1,3,[19,25,29,55,83]),
           'plus_U13':(3,1,5,[5,7,7,11,17,55,65,83]),
           'minus_cycle_5':(3,-1,1,[5,7]),
           'minus_cycle_17':(3,-1,4,[17,25,37,41,55,61,91]),
           'five_cycle_1':(5,1,3,[1,3]),
           'five_cycle_13':(5,1,4,[13,33,83])}
    unit_rows={}
    for name,(q,c,twos,sources) in units.items():
        k=len(sources)
        unit_rows[name]={'value':certificate(twos,sources,q,c)['value'],
                         'odd_labels':k,'twos':twos,
                         'q_pow_k_below_two_pow_steps':q**k < 2**(twos+k)}
    return {'conjugation_r_minus_u_equals_s_u':conjugate,
            'minus_five_hand_certificate':certificate(4,[11,25,37],3,-1),
            'supply':[supply(n,q,c,max_label) for q,c,n in
                      [(3,-1,5),(3,-1,17),(5,1,13),(5,1,17),(5,1,7)]],
            'cubic_twin':cubic_twin(4307989),
            'exchange_classes_below_300':{f'{q}x{c:+d}':exchanges(q,c,300)['exchange_classes']
                                          for q,c in [(3,1),(3,-1),(5,1)]},
            'units':unit_rows}


def main():
    if sys.argv[1:]==['test']:
        raise SystemExit(subprocess.call(['uv','run','--quiet','--with','pytest','--with','scipy',
            'python3','-m','pytest',str(Path(__file__).with_name('test_research_lifts.py')),'-q']))
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('certificate')
    p.add_argument('--twos',type=int,required=True)
    p.add_argument('--odd-sources',type=int,nargs='*',default=[])
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p=sub.add_parser('fate')
    p.add_argument('n',type=int)
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p=sub.add_parser('supply')
    p.add_argument('n',type=int)
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p.add_argument('--max-label',type=int,default=20000)
    p.add_argument('--prime-bound',type=int,default=60)
    p=sub.add_parser('exchanges')
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p.add_argument('--max-label',type=int,default=300)
    p=sub.add_parser('cubic-twin')
    p.add_argument('b',type=int)
    p=sub.add_parser('map-control')
    p.add_argument('--max-label',type=int,default=20000)
    p=sub.add_parser('pair-energy')
    p.add_argument('word')
    p.add_argument('--multiplier',type=int,default=3)
    p.add_argument('--offset',type=int,default=1)
    p=sub.add_parser('signed-fixed')
    p.add_argument('--odd-source',type=int,default=3)
    p.add_argument('--cutoff',type=int,default=64)
    p=sub.add_parser('multiplicative-fixed')
    p.add_argument('--cutoff',type=int,default=64)
    p=sub.add_parser('approx-fixed')
    p.add_argument('--depth',type=int,required=True)
    p.add_argument('--cutoff',type=int,default=1000)
    p=sub.add_parser('pair-discriminant')
    p.add_argument('word')
    p=sub.add_parser('discriminant-scan')
    p.add_argument('--depth',type=int,default=12)
    p=sub.add_parser('wild-five-repair')
    p.add_argument('n',type=int)
    p=sub.add_parser('nearly-positive-fixed')
    p.add_argument('--depth',type=int,required=True)
    p.add_argument('--cutoff',type=int,default=1000)
    p=sub.add_parser('gap-control')
    p.add_argument('--parameter',type=int,default=1)
    p=sub.add_parser('two-edge-repair')
    p.add_argument('--parameter',type=int,default=1)
    p=sub.add_parser('two-odd-fiber')
    p.add_argument('--ratio',default='7/16')
    p=sub.add_parser('odd-factor-fiber')
    p.add_argument('--ratio',required=True)
    p.add_argument('--count',type=int,required=True)
    p.add_argument('--least',type=int,default=1)
    p=sub.add_parser('unit-parity')
    p=sub.add_parser('dyadic-pair-ledger')
    p.add_argument('word')
    p=sub.add_parser('quadratic-path')
    p.add_argument('--sources',type=int,nargs='+',required=True)
    p.add_argument('--target',type=int,nargs='+',required=True)
    p.add_argument('--max-label',type=int,default=1000)
    p.add_argument('--max-states',type=int,default=2000)
    p=sub.add_parser('catalytic-seven')
    p=sub.add_parser('anchored-cut')
    p.add_argument('n',type=int)
    p.add_argument('--cutoff',type=int,default=1000)
    p=sub.add_parser('quadratic-neighbors')
    p.add_argument('label',type=int)
    p=sub.add_parser('unit-assisted-seven')
    p=sub.add_parser('palette-obstruction')
    p=sub.add_parser('controls')
    p.add_argument('--followup',action='store_true')
    p.add_argument('--structural',action='store_true')
    p.add_argument('--scan-depth',type=int,default=16)
    a=parser.parse_args()
    if a.command=='certificate': result=certificate(a.twos,a.odd_sources,a.multiplier,a.offset)
    elif a.command=='fate': result=orbit_fate(a.n,a.multiplier,a.offset)
    elif a.command=='supply':
        result=supply(a.n,a.multiplier,a.offset,a.max_label,a.prime_bound)
    elif a.command=='exchanges': result=exchanges(a.multiplier,a.offset,a.max_label)
    elif a.command=='cubic-twin': result=cubic_twin(a.b)
    elif a.command=='map-control': result=map_control(a.max_label)
    elif a.command=='pair-energy': result=pair_energy(a.word,a.multiplier,a.offset)
    elif a.command=='signed-fixed': result=signed_fixed(a.odd_source,a.cutoff)
    elif a.command=='multiplicative-fixed': result=multiplicative_fixed(a.cutoff)
    elif a.command=='approx-fixed': result=approximate_fixed(a.depth,a.cutoff)
    elif a.command=='pair-discriminant': result=pair_discriminant(a.word)
    elif a.command=='discriminant-scan': result=discriminant_scan(a.depth)
    elif a.command=='wild-five-repair': result=wild_five_repair(a.n)
    elif a.command=='nearly-positive-fixed': result=nearly_positive_fixed(a.depth,a.cutoff)
    elif a.command=='gap-control': result=gap_control(a.parameter)
    elif a.command=='two-edge-repair': result=two_edge_repair(a.parameter)
    elif a.command=='two-odd-fiber': result=two_odd_fiber(a.ratio)
    elif a.command=='odd-factor-fiber': result=odd_factor_fiber(a.ratio,a.count,a.least)
    elif a.command=='unit-parity': result=unit_parity()
    elif a.command=='dyadic-pair-ledger': result=dyadic_pair_ledger(a.word)
    elif a.command=='quadratic-path': result=quadratic_path(a.sources,a.target,a.max_label,a.max_states)
    elif a.command=='catalytic-seven': result=catalytic_seven()
    elif a.command=='anchored-cut': result=anchored_cut(a.n,a.cutoff)
    elif a.command=='quadratic-neighbors': result=quadratic_neighbors(a.label)
    elif a.command=='unit-assisted-seven': result=unit_assisted_seven()
    elif a.command=='palette-obstruction': result=palette_obstruction()
    elif a.structural:
        result={
            'unit_parity':unit_parity(),
            'cubic_component':quadratic_path([7,65,133],[13,19,29],1000,20),
            'catalyst_121':quadratic_path([7,65,133,121],[13,19,29,121],2000,500),
            'unit_assisted_repair':unit_assisted_seven(),
            'small_neighbors':[quadratic_neighbors(u) for u in [1,3,5,7]],
            'palette_obstruction':palette_obstruction(),
            'dyadic_ledger':dyadic_pair_ledger('11111000'),
            'sharp_anchors':[anchored_cut(n,64) for n in [3,7,8]],
        }
    elif a.followup:
        result={
            'local_repair':two_edge_repair(1),
            'local_repair_parameter_five':two_edge_repair(5),
            'complete_two_factor_fiber':two_odd_fiber('7/16'),
            'published_certificate_seventy_one':wild_five_repair(71),
            'gap_control':gap_control(1),
            'discriminant_scan':discriminant_scan(a.scan_depth),
            'positive_approximation':approximate_fixed(8,14000),
            'exact_nearly_positive_fixed':nearly_positive_fixed(8,14000),
        }
    else:
        result={
            'three_path':certificate(3,[3,5]),
            'nine_product_only':certificate(6,[3,3,5,5]),
            'nine_repaired':certificate(7,[9,7,11,17,13,5]),
            'positive_cycle':pair_energy('10'),
            'negative_cycle':pair_energy('110'),
            'rational_large_gaps':pair_energy('11111000'),
            'five_n_plus_one':pair_energy('1110000',5),
            'signed_fixed_control':signed_fixed(3,64),
            'multiplicative_map_control':multiplicative_fixed(64),
        }
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
