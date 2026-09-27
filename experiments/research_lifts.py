#!/usr/bin/env -S uv run --quiet python3
"""Exact controls for three Collatz research proposals, not a convergence test."""
from collections import Counter
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


def certificate(twos, odd_sources):
    """Check both commutative value and exact backward-path realization.

    A factor 2 is usable at any positive state.  A factor u/T(u) is usable
    only at T(u), where its backward edge leads to u.  Every factor is used.
    """
    if twos < 0 or any(u < 1 or u%2 == 0 for u in odd_sources):
        raise ValueError('need nonnegative twos and positive odd sources')
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
    pairs=[]
    for left in range(1,isqrt(total)+1):
        if total%left:
            continue
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


def main():
    if sys.argv[1:]==['test']:
        raise SystemExit(subprocess.call(['uv','run','--quiet','--with','pytest','python3','-m',
            'pytest',str(Path(__file__).with_name('test_research_lifts.py')),'-q']))
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('certificate')
    p.add_argument('--twos',type=int,required=True)
    p.add_argument('--odd-sources',type=int,nargs='*',default=[])
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
    p=sub.add_parser('controls')
    p.add_argument('--followup',action='store_true')
    p.add_argument('--scan-depth',type=int,default=16)
    a=parser.parse_args()
    if a.command=='certificate': result=certificate(a.twos,a.odd_sources)
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
