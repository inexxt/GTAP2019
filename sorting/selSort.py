def insSort(ll):
    n = len(ll)
    for i in range(n):
        for j in range(i + 1, n):
            if ll[i] > ll[j]:
                ll[i], ll[j] = ll[j], ll[i]
    return ll

def insSort2(ll):
    n = len(ll)
    for i in range(n):
        curMin = i
        for j in range(i + 1, n):
            if ll[curMin] > ll[j]:
                curMin = j
        ll[i], ll[curMin] = ll[curMin], ll[i]
    return ll

print(insSort([5,2,1,3,4]))

print(insSort2([5,2,1,3,4]))
