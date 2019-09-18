def encode(ll):
    lehmer = [8] * len(ll)

    for e, x in enumerate(ll):
        lehmer[e] = len([0 for y in ll[e+1:] if y < x])

    return lehmer


def decode(lehmer):
    n = len(lehmer)
    lot = list(range(n))
    ll = []
    for i in range(n):
        ll.append(lot[lehmer[i]])
        del lot[lehmer[i]]

    return [x + 1 for x in ll]


def prod(ll):
    t = 1
    for x in ll:
        t *= x
    return t


ll = [2, 5, 1, 3, 6, 4]
assert(decode(encode(ll)) == ll)

# 1 2 3 4 5 6
# 2 5 1 3 6 4 - perm
# 1 3 0 0 1 0 - lehmer

