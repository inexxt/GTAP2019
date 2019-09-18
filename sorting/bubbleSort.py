def bubbleSort(ll):
    n = len(ll)
    for i in range(n):
        for j in range(n-1):
            if ll[j] > ll[j+1]:
                ll[j], ll[j+1] = ll[j+1], ll[j]
    return ll

print(bubbleSort([5,2,1,3,4]))
