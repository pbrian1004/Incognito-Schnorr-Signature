import os
import secrets
import time
import numpy as np
import Crypto
from sympy import mod_inverse
from decimal import Decimal
from math import log2
from pprint import pprint
# if having trouble importing Crypto, try uninstall Crypto and install pycryptodome instead
from Crypto.Hash import SHA256
# On MacOS, install brew, then $brew install gmp$ after pip install fastecdsa
from fastecdsa import keys, curve, ecdsa
from hashlib import sha256, sha512, sha384
import sys

# To avoid ValueError: Exceeds the limit (4300) for integer string conversion
sys.set_int_max_str_digits(0)

# define basic parameter
my_curve = curve.P256
g = my_curve.G
p = my_curve.q
generator_u = g * secrets.randbelow(p)

new_curve1 = curve.P256
h = new_curve1.G


# define basic operation
# int(c, 16) is to convert hexadecmical strings to actual numbers, I don't think it would limit the size of the number
def A(r):
    return g * r
def Z(sk,r,c):
    c = int(c, 16)
    return (r + c*sk) % p
def V_z(z, pk, c):
    c = int(c, 16)
    return (g*z) - (pk*c)
def vector_addition(a, b):
    va = [None] * len(a)
    for i in range (len(a)):
        va[i] = a[i] + b[i]
    return va
def vector_minus(a, b):
    vm = [None] * len(a)
    for i in range (len(a)):
        vm[i] = a[i] - b[i]
    return vm
def hadamard_products(a, b):
    hp = [None] * len(a)
    for i in range (len(a)):
        hp[i] = a[i] * b[i]
    return hp
def hadamard_powers(base, power):
    hp = [None] * len(base)
    for i in range (len(base)):
        hp[i] = base[i] ** power[i]
    return hp
def inner_products(a, b):
    for i in range (len(a)):
        if i == 0:
            ip = a[i] * b[i]
        else:
            ip += a[i] * b[i]
    return ip
def consecutive_powers(y, n):
    yn = [None] * n
    for i in range (n):
        yn[i] = y ** i
    return yn
    
# setup function, not actually called since parameter are already defined
def Setup(parameter):
    return parameter, hash


# key generation calling ecc keyGen
def KeyGen():
#     sk is before pk
    return keys.gen_keypair(my_curve)


# converting a ecc point to string form: taking its x and y coodinates
def pt_to_string(point):
    a = str(point.x)
    b = str(point.y)
    return a + b

# helper method to convert a list of numbers to a string
def list_to_string(l):
    a = ''
    for i in range (len(l)):
        a = a + str(l[i])
############################################# set a = hash(a) before returning it #######  
    return a

def Schnorr_SIGN(m, sk):
    r = secrets.randbelow(p)
    R = A(r)
    my_string = m + pt_to_string(R)
    c = sha256(my_string.encode()).hexdigest()
    z = Z(sk,r,c)
    return z, c

def Schnorr_VERIFY(m, pk, sigma):
    z = sigma[0]
    c = sigma[1]
    R_prime = V_z(z, pk, c)
    my_string = m + pt_to_string(R_prime)
    x = sha256(my_string.encode()).hexdigest()
    if c != sha256(my_string.encode()).hexdigest():
        return 0
    return 1

for i in range (100):
    sk_temp, pk_temp = KeyGen()
    s = Schnorr_SIGN("i am ", sk_temp)
    if (Schnorr_VERIFY("i am ", pk_temp, s) == 0):
        print("failed")
        break

# basic sign without bulletproofs
def Sign(PK, j, sigma):
    z = sigma[0]
    c = sigma[1]
    universal_pk_string = list_to_string(PK)
    R = V_z(z, PK[j], c)
    b_array = [0] * len(PK)
    b_array[j] = 1
    a_array = [-1] * len(PK)
    a_array[j] = 0

    ### 1. Commit pkj
    g0 = sha256((c + universal_pk_string).encode()).hexdigest()
    g0 = int(g0, 16) * g
    beta = secrets.randbelow(p)
    Cpk = g0 * beta + PK[j]

    ### 2. ZK Proof for z
    rz = secrets.randbelow(p)
    rb = secrets.randbelow(p)
    c = int(c, 16)
    Rz = g * rz + g0 * rb * c
    cz = sha256((str(Rz) + str(Cpk)).encode()).hexdigest()
    cz = int(cz, 16)
    sz = (rz + cz * z) % p
    s_beta = (rb + cz * beta) % p
    pi_z = [Rz, sz, s_beta]

    ### 3. ZK Proof for b
    ##### generators h, (g1, ..., gn), and (h1, ..., hn) are all equals to g #####
    g_array = [None] * len(PK)
    h_array = [None] * len(PK)
    sa = [None] * len(PK)
    sb = [None] * len(PK)
    for i in range (len(PK)):
        new_curve2 = curve.P256
        g_array[i] = new_curve2.G
        new_curve3 = curve.P256
        h_array[i] = new_curve3.G
        sa[i] = secrets.randbelow(p)
        sb[i] = secrets.randbelow(p)

    alpha = secrets.randbelow(p)
    rho = secrets.randbelow(p)
    zeta = secrets.randbelow(p)
    A = h * alpha + inner_products(g_array, b_array) + inner_products(h_array, a_array)
    S = h * rho + inner_products(g_array, sb) + inner_products(h_array, sa)
    Spk = g0 * zeta + inner_products(PK, sb)
    y = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode()).hexdigest(), 16)
    w = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode()).hexdigest(), 16)

    yn = consecutive_powers(y, len(PK))
    t0 = (w ** 2) - (w ** 3)
    In = [1] * len(PK)
    wn = [w*i for i in In]
    w2n = [(w**2)*i for i in In]
    tau1 = secrets.randbelow(p)
    tau2 = secrets.randbelow(p)
    t1 = inner_products(sb, vector_addition(hadamard_products(yn, vector_addition(a_array, wn)), w2n)) 
    + inner_products(vector_minus(b_array, wn), hadamard_products(yn, sa))
    t2 = inner_products(sb, hadamard_products(yn, sa))
    T1 = g * t1 + h * tau1
    T2 = g * t2 + h * tau2

    x = int(sha256((str(T1) + str(T2) + str(y) + str(w)).encode()).hexdigest(), 16)
    Lx = vector_addition(vector_minus(b_array, wn), [x*i for i in sb])
    Rx = vector_addition(hadamard_products(yn, vector_addition([x*i for i in sa], vector_addition(a_array, wn))), w2n)
    tx = t0 + t1 * x + t2 * (x**2)
    tau_x = tau2 * (x**2) + tau1 * x
    mu = alpha + rho * x
    nu = beta + zeta * x
    pi_b = [A, S, Spk, T1, T2, tau_x, mu, nu, tx, Lx, Rx]

    return (R, Cpk, pi_z, pi_b)


def Verify(m, PK, sigma):
    R = sigma[0]
    Cpk = sigma[1]
    pi_z = sigma[2]
    pi_b = sigma[3]
    [Rz, sz, s_beta] = pi_z
    [A, S, Spk, T1, T2, tau_x, mu, nu, tx, Lx, Rx] = pi_b
    universal_pk_string = list_to_string(PK)    
    my_string = m + pt_to_string(R)
    c = sha256(my_string.encode()).hexdigest()
    g0 = sha256((c + universal_pk_string).encode()).hexdigest()
    g0 = int(g0, 16) * g
    c = int(c, 16)
    cz = sha256((str(Rz) + str(Cpk)).encode()).hexdigest()
    cz = int(cz, 16)
    
    if g*sz + g0*s_beta*c != Rz + R*cz + Cpk*c*cz:
        print('original pi_z verification failed')
        return 0    

    y = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode()).hexdigest(), 16)
    w = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode()).hexdigest(), 16)
    x = int(sha256((str(T1) + str(T2) + str(y) + str(w)).encode()).hexdigest(), 16)
    if g*tx + h*tau_x != g*((w ** 2) - (w ** 3)) + T1*x + T2*(x**2):
        print('original pi_b verification failed')
        return 0 

    return 1


# testing
PK_num = 20
for ii in range (0, PK_num):
    fake_PK = [None]* (PK_num)
    for i in range (0, PK_num):
    #     fill it with fake first, then change later
        foo, fake_PK[i] = KeyGen()
    ssk, ppk = KeyGen()
    my_sk, fake_PK[ii] = ssk, ppk
    hh = Schnorr_SIGN("I am ", my_sk)
    Incog = Sign(fake_PK, ii, hh)
    if Verify("I am ", fake_PK, Incog) != 1:
        print ("Incognito failed")


power_of_2 = 10
PK_num = 2 ** power_of_2
time_trail = 1
fake_PK = [None]* (PK_num)
for i in range (0, PK_num):
#     fill it with fake first, then change later
    foo, fake_PK[i] = KeyGen()
ssk, ppk = KeyGen()
for ii in range (time_trail):
    start_time = time.time()
    random_position = secrets.randbelow(PK_num)
    my_sk, fake_PK[random_position] = ssk, ppk
    hh = Schnorr_SIGN("I am ", my_sk)
    Incog = Sign(fake_PK, random_position, hh)
    if Verify("I am ", fake_PK, Incog) != 1:
        print ("Incognito failed")
        # break
    print('total time elaspsed ', time.time() - start_time)
