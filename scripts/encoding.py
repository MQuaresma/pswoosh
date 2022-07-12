#!/usr/bin/python3

import random

def binomial(k):
    a = random.randint(0,2**k-1)
    b = random.randint(0,2**k-1)
    r = 0
    for i in range(0,k):
        r += (a>>i) & 1
        r -= (b>>i) & 1
    return r


def es_noise(n, k):
    r = 0
    for i in range(0,n):
        r += binomial(k) * binomial(k)
    return r


def decode(x, q):
    x = x % q
    if x < q/4:
        return 0
    if x > (3*q)/4:
        return 0
    return 1


def decode16(coeffs, q):
    # simple majority voting:
    t = 0
    for i in range(0,15):
        t += decode(coeffs[i], q)
    if t < 8:
        return 0
    return 1
    # Very naive way; ignore 15 coeffs, just use first:
    return decode(coeffs[0], q)



q = 3329
n = 256
k = 4
max = 1024
failctr = 0
onectr = 0
zeroctr = 0

for i in range(0,max):
    alice = []
    bob   = []
    for j in range(0,16):
        ass = random.randint(0,q)
        alice.append(ass+es_noise(n,k))
        bob.append(ass+es_noise(n,k))
    x = decode16(alice, q)
    y = decode16(bob, q)
    if x != y:
        failctr += 1
    elif x == 1:
        onectr += 1
    else:
        zeroctr += 1

print("failed: "+str(failctr))
print("zeroes: "+str(zeroctr))
print("ones:   "+str(onectr))
