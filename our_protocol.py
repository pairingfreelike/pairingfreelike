from charm.toolbox.eccurve import prime192v1
from charm.toolbox.ecgroup import ECGroup
from charm.toolbox.ecgroup import G
import sys

class Like:	
    def __init__(self, groupObj, secparam=0):
        global group
        group = groupObj
        group.paramgen(secparam)
        global g
        g = group.random(G)
        global H
        H = group.hash
        
    def keygen_u(self):
        sk = group.random()	
        pk = g ** sk
        return (pk, sk)
    
    def keygen_a(self):
        sk = group.random()	
        pk1 = g ** sk
        pk2 = self.sokLog(sk, pk1)
        pk = {'pk1' : pk1, 'pk2' : pk2}
        return (pk, sk)

    def sokLog(self, x, h, M=0):
        r = group.random()
        R = g ** r
        c = H((R, h, M))
        z = r + x * c
        pi = {'pi1' : R, 'pi2' : z}
        return pi
    
    def vokLog(self, h, pi, M = 0):
        return (g ** pi['pi2'] == pi['pi1'] * (h ** H((pi['pi1'], h, M))))
    
    def sokLogEq(self, x, g1, g2, h1, h2, M = 0):
        r = group.random()
        R1 = g1 ** r
        R2 = g2 ** r
        c = H((R1, R2, g1, g2, h1, h2, M))
        z = r + x * c
        pi = {'pi1' : R1, 'pi2' : R2, 'pi3' : z}
        return pi
    
    def vokLogEq(self, g1, g2, h1, h2, pi, M = 0):
        c = H((pi['pi1'], pi['pi2'], g1, g2, h1, h2, M))
        return ((g1 ** pi['pi3'] == pi['pi1'] * (h1 ** c)) and (g2 ** pi['pi3'] == pi['pi2'] * (h2 ** c)))
    
    def precomp(self, pk_aut, pk_A, pk_B):
        for pk in pk_aut:
            if (self.vokLog(pk['pk1'], pk['pk2']) == False):
                    sys.exit("Error: authority keys invalid")
        h = pk_aut[0]['pk1']
        for i in range(1, len(pk_aut)):
            h = h * pk_aut[i]['pk1']
        w_tuple = (pk_A, pk_B)
        for pk in pk_aut:
            w_tuple = w_tuple + (pk['pk1'],)
        w = H(w_tuple)
        return (h,w)
    
    def A_step_1(self):
        x = group.random()
        X = g ** x
        return (x, X)
    
    def B_step_1(self, sk, pk_A, pk_B, X, h, w):
        y = group.random()
        Y = g ** y
        H_ = (h * X) ** y
        pi = self.sokLogEq(y, g, (h * X), Y, H_, w)
        msg = H((pk_A, pk_B, X, Y))
        sigma = self.sokLog(sk, pk_B, msg)
        return (y, Y, sigma, H_, pi)
    
    def A_step_2(self, sk, pk_A, pk_B, x, X, h, w, Y, sigma_B_1):
        msg = H((pk_A, pk_B, X, Y))
        if (self.vokLog(pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        H_ = (h * Y) ** x
        pi = self.sokLogEq(x, g, (h * Y), X, H_, w)
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        sigma = self.sokLog(sk, pk_A, msg)
        return (sigma, H_, pi)

    def B_step_2(self, sk, pk_A, pk_B, y, X, Y, sigma_B_1, sigma_A):
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        sigma = self.sokLog(sk, pk_B, msg)
        return sigma
        
    def A_out(self, x, Y):
        return (Y ** x)
    
    def B_out(self, y, X):
        return (X ** y)
    
    def OA_out(self, sk, pk, pk_A, pk_B, w, X, Y, sigma_B_1, sigma_A, sigma_B_2, h, H_, pi): 
        msg = H((pk_A, pk_B, X, Y))
        if (self.vokLog(pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of Bob invalid")
        if ( self.vokLogEq(g, (h * Y), X, H_, pi, w)  == False):
            sys.exit("Error: PoK of Alice invalid")
        msg = H((w, X, Y, H_, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2'], pi['pi1'], pi['pi2'], pi['pi3']))
        sigma = self.sokLog(sk, pk, msg)
        return sigma
            
    def OB_out(self, sk, pk, pk_A, pk_B, w, X, Y, sigma_B_1, sigma_A, sigma_B_2, h, H_, pi): 
        msg = H((pk_A, pk_B, X, Y))
        if (self.vokLog(pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of Bob invalid")
        if ( self.vokLogEq(g, (h * X), Y, H_, pi, w)  == False):
            sys.exit("Error: PoK of Bob invalid")
        msg = H((w, X, Y, H_, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2'], pi['pi1'], pi['pi2'], pi['pi3']))
        sigma = self.sokLog(sk, pk, msg)
        return sigma
    
    def sst_A_verif(self, pk_aut, pk_O, pk_A, pk_B, w, X, Y, sigma_B_1, sigma_A, sigma_B_2, h, H_, pi, sigma_O):
        for pk in pk_aut:
            if (self.vokLog(pk['pk1'], pk['pk2']) == False):
                    sys.exit("Error: authority keys invalid")
        msg = H((pk_A, pk_B, X, Y))
        if (self.vokLog(pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of B invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of A invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of B invalid")
        if ( self.vokLogEq(g, (h * Y), X, H_, pi, w)  == False):
            sys.exit("Error: PoK of A invalid")
        msg = H((w, X, Y, H_, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2'], pi['pi1'], pi['pi2'], pi['pi3']))
        if (self.vokLog(pk_O, sigma_O, msg) == False):
            sys.exit("Error: signature of OA invalid")
        return True
    
    def sst_B_verif(self, pk_aut, pk_O, pk_A, pk_B, w, X, Y, sigma_B_1, sigma_A, sigma_B_2, h, H_, pi, sigma_O):
        for pk in pk_aut:
            if (self.vokLog(pk['pk1'], pk['pk2']) == False):
                    sys.exit("Error: authority keys invalid")
        msg = H((pk_A, pk_B, X, Y))
        if (self.vokLog(pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((pk_A, pk_B, X, Y, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of Bob invalid")
        if ( self.vokLogEq(g, (h * X), Y, H_, pi, w)  == False):
            sys.exit("Error: PoK of Bob invalid")
        msg = H((w, X, Y, H_, sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2'], pi['pi1'], pi['pi2'], pi['pi3']))
        if (self.vokLog(pk_O, sigma_O, msg) == False):
            sys.exit("Error: signature of OB invalid")
        return True
    
    def td_gen(self, sk, pk, Z):
        td1 = Z ** sk
        td2 = self.sokLogEq(sk, g, Z, pk['pk1'], td1)
        td = {'td1' : td1, 'td2' : td2}
        return td
        
    def key_extract(self, td_list, pk_list, H_, Z):
        for i in range(len(td_list)):
            if (self.vokLogEq(g, Z, pk_list[i]['pk1'], td_list[i]['td1'], td_list[i]['td2']) == False):
                    sys.exit("Error: trapdoors invalid")
        K = H_
        for td in td_list:
            K = K / td['td1']
        return K
        

n = 10
m = 10

print("Number of authorities (Alice side):", n)
print("Number of authorities (Bob side):", m)

print("Initialisation:")
groupObj = ECGroup(prime192v1)
li = Like(groupObj)
print("Done")

print("Keys generation:")
(pk_OA, sk_OA) = li.keygen_u()
(pk_OB, sk_OB) = li.keygen_u()
(pk_A, sk_A) = li.keygen_u()
(pk_B, sk_B) = li.keygen_u()
pk_aut_A = []
sk_aut_A = []
for i in range(n):
    (pk, sk) = li.keygen_a()
    pk_aut_A.append(pk)
    sk_aut_A.append(sk)

pk_aut_B = []
sk_aut_B = []
for i in range(m):
    (pk, sk) = li.keygen_a()
    pk_aut_B.append(pk)
    sk_aut_B.append(sk)
print("Done")

print("Alice precomputation:")
(h_A, w_A) = li.precomp(pk_aut_A, pk_A, pk_B)
print("Done")

print("Bob precomputation :")
(h_B, w_B) = li.precomp(pk_aut_B, pk_A, pk_B)
print("Done")

print("Protocol:")
(x, X) = li.A_step_1()
(y, Y, sigma_B_1, H_B, pi_B) = li.B_step_1(sk_B, pk_A, pk_B, X, h_B, w_B)
(sigma_A, H_A, pi_A) = li.A_step_2(sk_A, pk_A, pk_B, x, X, h_A, w_A, Y, sigma_B_1)
sigma_B_2 = li.B_step_2(sk_B, pk_A, pk_B, y, X, Y, sigma_B_1, sigma_A)
K_A = li.A_out(x, Y)
K_B = li.B_out(y, X) 

sigma_OA = li.OA_out(sk_OA, pk_OA, pk_A, pk_B, w_A, X, Y, sigma_B_1, sigma_A, sigma_B_2, h_A, H_A, pi_A)
sigma_OB = li.OB_out(sk_OB, pk_OB, pk_A, pk_B, w_B, X, Y, sigma_B_1, sigma_A, sigma_B_2, h_B, H_B, pi_B)
print("Done")

print("Check that Alice and Bob share the same key:", K_A == K_B)

print("Operator states verification")
li.sst_A_verif(pk_aut_A, pk_OA, pk_A, pk_B, w_A, X, Y, sigma_B_1, sigma_A, sigma_B_2, h_A, H_A, pi_A, sigma_OA)
li.sst_B_verif(pk_aut_B, pk_OB, pk_A, pk_B, w_B, X, Y, sigma_B_1, sigma_A, sigma_B_2, h_B, H_B, pi_B, sigma_OB)
print("Done")

print("Trapdoors generation (Alice side)")
td_A = []
for i in range(n):
    td = li.td_gen(sk_aut_A[i], pk_aut_A[i], X)
    td_A.append(td)
print("Done")

print("Trapdoors generation (Alice side)")
td_B = []
for i in range(m):
    td = li.td_gen(sk_aut_B[i], pk_aut_B[i], Y)
    td_B.append(td)
print("Done")

print("Alice's key extraction:")
K_A_e = li.key_extract(td_A, pk_aut_A, H_A, X)
print("Done")
print("Check that the ALice's extracted key is correct:", K_A == K_A_e)

print("Bob's key extraction:")
K_B_e = li.key_extract(td_B, pk_aut_B, H_B, Y)
print("Done")

print("Check that the Bob's extracted key is correct:", K_A == K_A_e)
print("Program termination: success")

