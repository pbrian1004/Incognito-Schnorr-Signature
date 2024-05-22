import os
import secrets
import time
# On MacOS, install brew, then $brew install gmp$ after pip install fastecdsa
from fastecdsa import keys
from fastecdsa.curve import secp256k1, Curve
from src.innerproduct.inner_product_prover import NIProver
from src.innerproduct.inner_product_verifier import Verifier1
from src.utils.utils import point_to_bytes, bytes_to_point, mod_hash, ModP
from src.utils.elliptic_curve_hash import elliptic_hash
from src.utils.commitments import vector_commitment


# To avoid ValueError: Exceeds the limit (4300) for integer string conversion
#sys.set_int_max_str_digits(0)

def hash_to_point(m: str):
    return elliptic_hash(m.encode(), my_curve) 

# define basic parameter
CURVE: Curve = secp256k1

my_curve = CURVE
g = my_curve.G
p = my_curve.q
generator_u = hash_to_point("Incognito.u")
h = hash_to_point("Incognito.h")
MAXPKSIZE = 2048 # maximum number of mixin supported is defined here. It affects the number of public parameters generated
gvec = [None] * MAXPKSIZE
hvec = [None] * MAXPKSIZE
for i in range (MAXPKSIZE):
    gvec[i] = hash_to_point(str(i)+"Incognito.g")
    hvec[i] = hash_to_point(str(i)+"Incognito.h")

# define Schnorr signature functions
def A(r):
    return r * g
def Z(sk,r,c):
    return r + c*sk
def V_z(z, pk, c):
    return (z*g) - (c*pk)
# define basic maths operation
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
# def hadamard_add(a, b):
#     hp = [None] * len(a)
#     for i in range (len(a)):
#         hp[i] = a[i] + b[i]
#     return hp
def hadamard_products(a, b):
    hp = [None] * len(a)
    for i in range (len(a)):
        hp[i] = a[i] * b[i]
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
    yn[0] = ModP(1,p)
    for i in range (1,n):
        yn[i] = y * yn[i-1]
    return yn
def consecutive_inv_powers(y, n):
    yn = [None] * n
    yn[0] = ModP(1,p)
    yinv = ModP.inv(y)
    for i in range (1,n):
        yn[i] = yn[i-1] * yinv
    return yn
def hash_bytes_to_point(m: bytes):
    return elliptic_hash(m, my_curve) 
def rand_modp():
    return ModP(secrets.randbelow(p),p);

# setup function, creating secure generators from hash_to_point, so that the DL of generators are hidden
def Setup():
    return (gvec, hvec, generator_u, h)

# receiving system parametes and saving it locally
def Setup_r(param):
    gvec = param[0]
    hvec = param[1]
    generator_u = param[2]
    h = param[3]
    return

# key generation calling ecc keyGen
def KeyGen():
#     sk is before pk
    return keys.gen_keypair(my_curve)

# helper method to convert a list of numbers to a string
def list_to_string(l):
    a = ''
    for i in range (len(l)):
        a = a + str(l[i])
############################################# set a = hash(a) before returning it #######  
    return a

def Schnorr_SIGN(m, sk):
    r = rand_modp()
    R = A(r)
    c = mod_hash(m.encode() + point_to_bytes(R),p)
    skp = ModP(sk, p)
    z = Z(skp,r,c)
    return z, c

def Schnorr_VERIFY(m, pk, sigma):
    z = sigma[0]
    c = sigma[1]
    R_prime = V_z(z, pk, c)
    x = mod_hash(m.encode() + point_to_bytes(R_prime),p)
    if c != x:
        return 0
    return 1

def testSchnorr():
    for i in range (1):
        sk_temp, pk_temp = KeyGen()
        s = Schnorr_SIGN("i am ", sk_temp)
        if (Schnorr_VERIFY("i am ", pk_temp, s) == 0):
            print("failed")
            break
    return

# sign
def Sign(PK, j, sigma):
    if (len(PK) > MAXPKSIZE):
        raise ValueError("The PK set size is larger than the maximum size.")
    z = sigma[0]
    c = sigma[1]
    universal_pk_string = list_to_string(PK)
    R = V_z(z, PK[j], c)
    b_array = [ModP(0,p)] * len(PK)
    b_array[j] = ModP(1,p)
    a_array = [ModP(-1,p)] * len(PK)
    a_array[j] = ModP(0,p)

    ### 1. Commit pkj
    g0 = hash_to_point((str(c) + universal_pk_string))
    beta = rand_modp()
    Cpk = beta * g0 + PK[j]

    ### 2. ZK Proof for z
    rz = rand_modp()
    rb = rand_modp()
    rbc = rb * c
    Rz = rz * g + rbc * g0
    cz = mod_hash((str(Rz) + str(Cpk)).encode(),p)
    sz = (rz + cz * z)
    s_beta = (rb + cz * beta)
    pi_z = [point_to_bytes(Rz), sz, s_beta]

    ### 3. ZK Proof for b
    g_array = [None] * len(PK)
    h_array = [None] * len(PK)
    sa = [None] * len(PK)
    sb = [None] * len(PK)
    for i in range (len(PK)):
        g_array[i] = gvec[i]
        h_array[i] = hvec[i]
        sa[i] = rand_modp()
        sb[i] = rand_modp()

    alpha = rand_modp()
    rho = rand_modp()
    zeta = rand_modp()
    #A = alpha * h + inner_products(b_array, g_array) + inner_products(a_array, h_array)
    A = alpha * h + vector_commitment(g_array, h_array, b_array, a_array)
    #S = rho * h + inner_products(sb, g_array) + inner_products(sa, h_array)
    S = rho * h + vector_commitment(g_array, h_array, sb, sa)
    Spk = zeta * g0 + inner_products(sb, PK)
    y = mod_hash((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode(),p)
    w = mod_hash((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode(),p)

    yn = consecutive_powers(y, len(PK))
    In = [ModP(1,p)] * len(PK)
    t0 = (w * w) - (w ** 3)* ModP(len(PK),p) + (w - w *w) * inner_products(yn, In)
    wn = [w*i for i in In] 
    w2n = [(w * w)*i for i in In]
    tau1 = rand_modp()
    tau2 = rand_modp()
    a_plus_wn = vector_addition(a_array, wn)
    b_minus_wn = vector_minus(b_array, wn)
    t1 = inner_products(sb, vector_addition(hadamard_products(yn, a_plus_wn), w2n)) + inner_products(b_minus_wn, hadamard_products(yn, sa)) 
    t2 = inner_products(sb, hadamard_products(yn, sa))
    T1 = t1 * g + tau1 * h
    T2 = t2 * g + tau2 * h

    x = mod_hash((str(T1) + str(T2) + str(y) + str(w)).encode(),p)
    Lx = vector_addition(b_minus_wn, [x*i for i in sb])
    Rx = vector_addition(hadamard_products(yn, vector_addition([x*i for i in sa], a_plus_wn)), w2n)
    tx = t0 + t1 * x + t2 * (x * x)
    tau_x = tau2 * (x * x) + tau1 * x 
    mu = alpha + rho * x
    nu = beta + zeta * x
    #pi_b = [A, S, Spk, T1, T2, tau_x, mu, nu, tx, Lx, Rx]

    ### 4. start Bulletproof here
    hinv_array = hadamard_products(consecutive_inv_powers(y, len(PK)),h_array)
    d = mod_hash((str(x) + str(tau_x) + str(mu) + str(nu) + str(tx)).encode(),p)
    g_bullet = vector_addition(g_array,[d*i for i in PK])
    #P = inner_products(Lx, g_bullet) + inner_products(Rx, hinv_array) 
    P = vector_commitment(g_bullet, hinv_array, Lx, Rx) 

    Prov = NIProver(g_bullet, hinv_array, generator_u, P, tx, Lx, Rx, CURVE, secrets.token_bytes(10))
    proof = Prov.prove()
    pi_B = [point_to_bytes(A), point_to_bytes(S), point_to_bytes(Spk), point_to_bytes(T1), point_to_bytes(T2), tau_x, mu, nu, tx, proof]

    return (point_to_bytes(R), point_to_bytes(Cpk), pi_z, pi_B)


def Verify(m, PK, sigma):
    # setting up the curve to prevent unknown bug of curve mismatch when sending the signature via socket
    my_curve = PK[0].curve
    g.curve = PK[0].curve
    h.curve = PK[0].curve
    generator_u.curve = PK[0].curve

    R_bytes = sigma[0]
    R = bytes_to_point(R_bytes)
    R.curve = PK[0].curve
    Cpk_bytes = sigma[1]
    Cpk = bytes_to_point(Cpk_bytes)
    Cpk.curve = PK[0].curve
    pi_z = sigma[2]
    pi_B = sigma[3]
    [Rzbytes, sz, s_beta] = pi_z
    Rz = bytes_to_point(Rzbytes)
    Rz.curve = PK[0].curve

    [A_bytes, S_bytes, Spk_bytes, T1_bytes, T2_bytes, tau_x, mu, nu, tx, proof] = pi_B
    A = bytes_to_point(A_bytes)
    A.curve = PK[0].curve
    S = bytes_to_point(S_bytes)
    S.curve = PK[0].curve
    Spk = bytes_to_point(Spk_bytes)
    Spk.curve = PK[0].curve
    T1 = bytes_to_point(T1_bytes)
    T1.curve = PK[0].curve
    T2 = bytes_to_point(T2_bytes)
    T2.curve = PK[0].curve
    universal_pk_string = list_to_string(PK)    
    c = mod_hash(m.encode() + point_to_bytes(R),p)
    g0 = hash_to_point((str(c) + universal_pk_string))
    g0.curve = PK[0].curve
    cz = mod_hash((str(Rz) + str(Cpk)).encode(),p)
    
    if sz * g + (s_beta*c) * g0!= Rz + cz * R + (c * cz) * Cpk:
        print('original pi_z verification failed')
        return 0    

    y = mod_hash((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(1)).encode(),p)
    w = mod_hash((str(A) + str(S) + str(Spk) + str(g0) + str(Cpk) + str(2)).encode(),p)
    x = mod_hash((str(T1) + str(T2) + str(y) + str(w)).encode(),p)
    yn = consecutive_powers(y, len(PK))
    In = [ModP(1,p)] * len(PK)
    if tau_x * h != ((w * w) - (w ** 3 * ModP(len(PK),p)) + (w - w * w) * inner_products(yn, In) - tx) * g + x * T1 + (x * x) * T2:
        print('original pi_b verification failed')
        return 0 

    # if tx != inner_products(Lx, Rx):
    #    print('original t_x verification failed in verify.')
    #    return 0

    # # try verify equation 5 and 6 for programming check. They will be replaced by Bulletproof in the real incognito signature scheme. 
    # if (g0 * nu + inner_products(PK, Lx)) != (Cpk - inner_products(PK, In) * w + Spk * x):
    #    print('original Eq 6 verification failed')
    #    return 0
       
    g_array = [None] * len(PK)
    h_array = [None] * len(PK)
    for i in range (len(PK)):
        g_array[i] = gvec[i]
        h_array[i] = hvec[i]
        g_array[i].curve = PK[i].curve
        h_array[i].curve = PK[i].curve
        #PK[i].curve = h_array[i].curve
    hinv_array = hadamard_products(consecutive_inv_powers(y, len(PK)),h_array)
#    if (h * mu + inner_products(g_array, Lx) + inner_products(hinv_array, Rx)) != (A + S * x - inner_products(g_array, In) * w + inner_products(hinv_array,[(w*i + w**2) %p for i in yn])):
#        print('original Eq 5 verification failed')
#        return 0
# end verify equation 5 and 6 for programming check.  

# test verification of Bulletproof
    d = mod_hash((str(x) + str(tau_x) + str(mu) + str(nu) + str(tx)).encode(),p)
    g_bullet = vector_addition(g_array,[d*i for i in PK])
#    P = A + S * x + Cpk * d + Spk * (x * d % p) - inner_products(g_bullet, [w*i %p for i in In]) + inner_products(hinv_array,[(w*i + w**2) %p for i in yn]) - g0 * (nu * d % p) - h * mu
    P = A + x * S + w * inner_products(In, vector_minus(h_array, g_array)) + (w * w) * inner_products(In, hinv_array) - mu * h + d * (Cpk - w * inner_products(In, PK) + x * Spk - nu * g0)
    Verif = Verifier1(g_bullet, hinv_array, generator_u, P, tx, proof)
    Verif.proof1.P_new.curve = PK[0].curve
    Verif.proof1.u_new.curve = PK[0].curve
    if Verif.verify() == 0:
        print('Bulletproof verification failed')
        return 0
    return 1


# testing
def testIncognito():
    PK_num = 1
    Setup()
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
            print ("Incognito failed at loop " + str(ii))

    for power_of_2 in range (0,12):
        sign_sum = 0
        convert_sum = 0
        verify_sum = 0
        PK_num = 2 ** power_of_2
        time_trail = 100
        fake_PK = [None]* (PK_num)
        for i in range (0, PK_num):
        #     fill it with fake first, then change later
            foo, fake_PK[i] = KeyGen()
        ssk, ppk = KeyGen()
        for ii in range (time_trail):
            random_position = secrets.randbelow(PK_num)
            my_sk, fake_PK[random_position] = ssk, ppk
            start_time = time.time()
            hh = Schnorr_SIGN("I am ", my_sk)
            sign_sum += time.time() - start_time
            convert_start = time.time()
            Incog = Sign(fake_PK, random_position, hh)
            convert_sum += time.time() - convert_start
            verify_start = time.time()
            if Verify("I am ", fake_PK, Incog) != 1:
                print ("Incognito failed")
            verify_sum += time.time() - verify_start 
        sign_average = sign_sum / time_trail
        convert_average = convert_sum / time_trail
        verify_average = verify_sum / time_trail 
        print(str(2 ** power_of_2) + '. Local Sign: ' + str(sign_average)  + '. Convert: ' + str(convert_average) + ', Verify: ' + str(verify_average))
    return


# test remote sign
def test_remote_sign(PK_num):
    #param = Setup()
    sign_sum = 0
    convert_sum = 0
    fake_PK = [None]* (PK_num)
    for i in range (0, PK_num):
        #     fill it with fake first, then change later
        foo, fake_PK[i] = KeyGen()
    ssk, ppk = KeyGen()
    random_position = secrets.randbelow(PK_num)
    my_sk, fake_PK[random_position] = ssk, ppk
    start_time = time.time()
    hh = Schnorr_SIGN("Test inocgnito sign ", my_sk)
    sign_sum += time.time() - start_time
    convert_start = time.time()
    Incog = Sign(fake_PK, random_position, hh)
    convert_sum += time.time() - convert_start
    print(str(PK_num) + '. Remote Sign: ' + str(sign_sum)  + '. Convert: ' + str(convert_sum))
    return (Incog, fake_PK, sign_sum, convert_sum)

def test_remote_verify(Incog, fake_PK):
    #Setup_r(param)
    my_curve = fake_PK[0].curve
    verify_start = time.time()
    if Verify("Test inocgnito sign ", fake_PK, Incog) != 1:
        print ("Incognito failed")
    verify_time = time.time() - verify_start 
    print('Remote Verify: ' + str(verify_time))
    return verify_time
