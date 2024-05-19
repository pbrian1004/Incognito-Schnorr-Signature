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
h = g * secrets.randbelow(p)


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
def inner_products_zp(a, b):
    ip = 0
    for i in range (len(a)):
        ip = (a[i] * b[i] + ip) % p
    return ip
def inner_products_point(a, b):
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
def inverse_consecutive_powers(y, n):
    yn = [None] * n
    for i in range (n):
        yn[i] = y ** -i
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
    Rz = g * rz + g0 * ((rb * c)%p)
    cz = sha256((str(Rz) + str(Cpk)).encode()).hexdigest()
    cz = (int(cz, 16)) % p
    sz = (rz + cz * z) % p
    s_beta = (rb + cz * beta) % p
    pi_z = [Rz, sz, s_beta]

    ### 3. ZK Proof for b
    sa = [None] * len(PK)
    sb = [None] * len(PK)
    for i in range (len(PK)):
        sa[i] = secrets.randbelow(p)
        sb[i] = secrets.randbelow(p)

    alpha = secrets.randbelow(p)
    rho = secrets.randbelow(p)
    zeta = secrets.randbelow(p)
    A = h * alpha + inner_products_point(g_array, b_array) + inner_products_point(h_array, a_array)
    S = h * rho + inner_products_point(g_array, sb) + inner_products_point(h_array, sa)
    Spk = g0 * zeta + inner_products_point(PK, sb)
    y = (int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode()).hexdigest(), 16)) % p
    w = (int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode()).hexdigest(), 16)) % p

    yn = consecutive_powers(y, len(PK))
    In = [1] * len(PK)
    wn = [w*i for i in In]
    w2n = [(w**2)*i for i in In]
    tau1 = secrets.randbelow(p)
    tau2 = secrets.randbelow(p)
    t0 = (w**2) - (w**3)*len(PK) + (w - w**2)*inner_products_zp(In, yn)
    t1 = inner_products_zp(sb, vector_addition(hadamard_products(yn, vector_addition(a_array, wn)), w2n)) + inner_products_zp(vector_minus(b_array, wn), hadamard_products(yn, sa))
    t2 = inner_products_zp(sb, hadamard_products(yn, sa))
    T1 = g * t1 + h * tau1
    T2 = g * t2 + h * tau2

    x = (int(sha256((str(T1) + str(T2) + str(y) + str(w)).encode()).hexdigest(), 16)) % p
    Lx = vector_addition(vector_minus(b_array, wn), [x*i for i in sb])
    Rx = vector_addition(hadamard_products(yn, vector_addition([x*i for i in sa], vector_addition(a_array, wn))), w2n)
    tx = (t0 + t1 * x + t2 * (x**2)) % p
    tau_x = (tau2 * (x**2) + tau1 * x) % p
    mu = (alpha + rho * x) % p
    nu = (beta + zeta * x) % p
    # d = (int(sha256((str(x) + str(tau_x) + str(mu) + str(nu) + str(tx)).encode()).hexdigest(), 16)) % p
    # dn = [d*i for i in In]
    # iyn = inverse_consecutive_powers(y, len(PK))
    # h_ = hadamard_products(h_array, iyn)
    # P = inner_products_point(vector_addition(hadamard_products(PK, dn), g_array), Lx) + inner_products_point(h_, Rx)
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
    cz = (int(cz, 16)) % p
    y = (int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode()).hexdigest(), 16)) % p
    In = [1] * len(PK)
    yn = consecutive_powers(y, len(PK))
    
    if g*sz + g0*s_beta*c != Rz + R*cz + Cpk*c*cz:
        print('original pi_z verification failed')
        return 0    

    y = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode()).hexdigest(), 16)
    w = int(sha256((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode()).hexdigest(), 16)
    x = int(sha256((str(T1) + str(T2) + str(y) + str(w)).encode()).hexdigest(), 16)
    if g*tx + h*tau_x != g*((w**2) - (w**3)*len(PK) + (w - w**2)*inner_products_zp(In, yn)) + T1*x + T2*(x**2):
        print('original pi_b verification failed')
        return 0 

    if tx != inner_products_zp(Lx, Rx):
        print('original t_x verification failed')
        return 0
        
    return 1

# testing
PK_num = 20
g_array = [None] * PK_num
h_array = [None] * PK_num
for i in range (PK_num):
    g_array[i] = g * secrets.randbelow(p)
    h_array[i] = g * secrets.randbelow(p)
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

for power_of_2 in range (0, 12):
    sign_sum = 0
    verify_sum = 0
    PK_num = 2 ** power_of_2
    time_trail = 1
    g_array = [None] * PK_num
    h_array = [None] * PK_num
    for i in range (PK_num):
        g_array[i] = g * secrets.randbelow(p)
        h_array[i] = g * secrets.randbelow(p)
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
        sign_sum += time.time() - start_time
        verify_start = time.time()
        if Verify("I am ", fake_PK, Incog) != 1:
            print ("Incognito failed")
        verify_sum += time.time() - verify_start
        
    sign_average = sign_sum / time_trail
    verify_average = verify_sum / time_trail 
    print(str(2 ** power_of_2) + '. Basic Sign: ' + str(sign_average) + ', Basic Verify: ' + str(verify_average))


# For Bulletproofs testing in Python, we need to download the python-bulletproofs package from https://github.com/wborgeaud/python-bulletproofs.
# The Bulletproofs are only used to simulate the total implementation time, it doesn't interact with the Incognito Schnorr Signature.
# Because PK = sk * G in the fastecdsa, the original P = (g ◦ pk^d)^l * h′^r becomes P = ⟨g + pk · d, l⟩ + ⟨h′, r⟩.
# To implement Bulletproofs on Incognito Signature, replacing the exponent of witness l, r with the inner product is necessary as mentioned above.

from src.innerproduct.inner_product_prover import *
from src.innerproduct.inner_product_verifier import *
from src.tests.test_innerprod import *

def bulletproofs_sign(N):
    seeds = [os.urandom(10) for _ in range(6)]
    point = CURVE.q
    g = [elliptic_hash(str(i).encode() + seeds[0], CURVE) for i in range(N)]
    h = [elliptic_hash(str(i).encode() + seeds[1], CURVE) for i in range(N)]
    u = elliptic_hash(seeds[2], CURVE)
    a = [mod_hash(str(i).encode() + seeds[3], point) for i in range(N)]
    b = [mod_hash(str(i).encode() + seeds[4], point) for i in range(N)]
    P = vector_commitment(g, h, a, b)
    c = inner_product(a, b)
    Prov = NIProver(g, h, u, P, c, a, b, CURVE, seeds[5])
    proof = Prov.prove()
    parameters = [g, h, u, P, c]
    return parameters, proof

def bulletproofs_verify(sigma):
    parameters = sigma[0]
    proof = sigma[1]
    [g, h, u, P, c] = parameters
    Verif = Verifier1(g, h, u, P, c, proof)
    return Verif.verify()

for power_of_2 in range (0, 12):
    sign_sum = 0
    verify_sum = 0
    PK_num = 2 ** power_of_2
    time_trail = 100
    g_array = [None] * PK_num
    h_array = [None] * PK_num
    for i in range (PK_num):
        g_array[i] = g * secrets.randbelow(p)
        h_array[i] = g * secrets.randbelow(p)
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
        test_only_bulletproofs = bulletproofs_sign(PK_num)
        sign_sum += time.time() - start_time
        verify_start = time.time()
        if Verify("I am ", fake_PK, Incog) != 1:
            print ("Incognito failed")
        if not bulletproofs_verify(test_only_bulletproofs):
            print ("Bulletproofs failed")
        verify_sum += time.time() - verify_start
        
    sign_average = sign_sum / time_trail
    verify_average = verify_sum / time_trail 
    print(str(2 ** power_of_2) + '. Full Sign: ' + str(sign_average) + ', Full Verify: ' + str(verify_average))
