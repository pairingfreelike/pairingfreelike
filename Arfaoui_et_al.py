from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,pair
from charm.core.engine.util import objectToBytes
import sys

class Like:	
    def __init__(self, groupObj):
        global group
        group = groupObj
        global g1
        g1 = group.random(G1)
        global g2
        g2 = group.random(G2)
        global H
        H = group.hash
        
    def keygen_u(self):
        sk = group.random()	
        pk = g1 ** sk
        return (pk, sk)
    
    def keygen_a(self):
        sk = group.random()	
        pk1 = g1 ** sk
        pk2 = self.sokLog(sk, g1, pk1)
        pk = {'pk1' : pk1, 'pk2' : pk2}
        return (pk, sk)

    def sokLog(self, x, g, h, M=0):
        r = group.random()
        R = g ** r
        c = H((R, h, M))
        z = r + x * c
        pi = {'pi1' : R, 'pi2' : z}
        return pi
    
    def vokLog(self, g, h, pi, M=0):
        return (g ** pi['pi2'] == pi['pi1'] * (h ** H((pi['pi1'], h, M))))
    
    def sokLogEq(self, x, f1, f2, h1, h2, M=0):
        r = group.random()
        R1 = f1 ** r
        R2 = f2 ** r
        c = H((R1, R2, f1, f2, h1, h2, M))
        z = r + x * c
        pi = {'pi1' : R1, 'pi2' : R2, 'pi3' : z}
        return pi
    
    def vokLogEq(self, f1, f2, h1, h2, pi, M=0):
        c = H((pi['pi1'], pi['pi2'], f1, f2, h1, h2, M))
        return ((f1 ** pi['pi3'] == pi['pi1'] * (h1 ** c)) and (f2 ** pi['pi3'] == pi['pi2'] * (h2 ** c)))
    
    def precomp(self, pk_aut, pk_A, pk_B):
        for pk in pk_aut:
            if (self.vokLog(g1, pk['pk1'], pk['pk2']) == False):
                    sys.exit("Error: authority keys invalid")
        h = pk_aut[0]['pk1']
        for i in range(1, len(pk_aut)):
            h = h * pk_aut[i]['pk1']
        w_tuple = (pk_A, pk_B)
        for pk in pk_aut:
            w_tuple = w_tuple + (pk['pk1'],)
        w = H(w_tuple)
        return (h,w)
    
    def A_step_1(self, w):
        x = group.random(ZR)
        X1 = g1 ** x
        X2 = g2 ** x
        pi = self.sokLog(x, g2, X2, w)
        return (x, X1, X2, pi)
    
    def B_step_1(self, sk, pk, w, X1, X2, pi_A):
        if (self.vokLog(g2, X2, pi_A, w) == False):
            sys.exit("Error: PoK of Alice invalid")
        if (pair(X1,g2) != pair(g1,X2)):
            sys.exit("Error : e(X1,g2) =/= e(g1,X2)")
        y = group.random(ZR)
        Y = g2 ** y
        pi = self.sokLog(y, g2, Y, w)
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi['pi1'], pi['pi2']))
        sigma = self.sokLog(sk, g1, pk, msg)
        return (y, Y, sigma, pi)
    
    def A_step_2(self, sk, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1):
        if (self.vokLog(g2, Y, pi_B, w) == False):
            sys.exit("Error: PoK of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2']))
        if (self.vokLog(g1, pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2']))
        sigma = self.sokLog(sk, g1, pk_A, msg)
        return sigma
    
    def B_step_2(self, sk, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A):
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(g1, pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        sigma = self.sokLog(sk, g1, pk_B, msg)
        return sigma
        
    def A_out(self, h, x, Y):
        return (pair(h,Y) ** x)
    
    def B_out(self, h, y, X2):
        return (pair(h,X2) ** y)
    
    def O_out(self, sk, pk, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A, sigma_B_2): 
        if (self.vokLog(g2, X2, pi_A, w) == False):
            sys.exit("Error: PoK of Alice invalid")
        if (pair(X1,g2) != pair(g1,X2)):
            sys.exit("Error : e(X1,g2) =/= e(g1,X2)")
        if (self.vokLog(g2, Y, pi_B, w) == False):
            sys.exit("Error: PoK of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2']))
        if (self.vokLog(g1, pk_B, sigma_B_1, msg) == False):
            sys.exit("Error: first signature of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(g1, pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(g1, pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2']))
        sigma = self.sokLog(sk, g1, pk, msg)
        return sigma
    
    def sst_verif(self, pk_aut, pk_O, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A, sigma_B_2, sigma_O): 
        for pk in pk_aut:
            if (self.vokLog(g1, pk['pk1'], pk['pk2']) == False):
                    sys.exit("Error: authority keys invalid")
        if (self.vokLog(g2, X2, pi_A, w) == False):
            sys.exit("Error: PoK of Alice invalid")
        if (pair(X1,g2) != pair(g1,X2)):
            sys.exit("Error : e(X1,g2) =/= e(g1,X2)")
        if (self.vokLog(g2, Y, pi_B, w) == False):
            sys.exit("Error: PoK of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2']))
        if (self.vokLog(g1, pk_B, sigma_B_1, msg) == False):
           sys.exit("Error: first signature of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2']))
        if (self.vokLog(g1, pk_A, sigma_A, msg) == False):
            sys.exit("Error: signature of Alice invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2']))
        if (self.vokLog(g1, pk_B, sigma_B_2, msg) == False):
            sys.exit("Error: second signature of Bob invalid")
        msg = H((w, X1, X2, Y, pi_A['pi1'], pi_A['pi2'], pi_B['pi1'], pi_B['pi2'], sigma_B_1['pi1'], sigma_B_1['pi2'], sigma_A['pi1'], sigma_A['pi2'], sigma_B_2['pi1'], sigma_B_2['pi2']))
        if (self.vokLog(g1, pk_O, sigma_O, msg) == False):
            sys.exit("Error: signature of the operator invalid")
        return True
    
    def td_gen(self, sk, pk, X1, Y):
        gt = pair(X1,Y)
        td1 = gt ** sk
        td2 = self.sokLogEq(sk, g1, gt, pk['pk1'], td1)
        td = {'td1' : td1, 'td2' : td2}
        return td
        
    def key_extract(self, td_list, pk_list, X1, Y):
        gt = pair(X1,Y)
        for i in range(len(td_list)):
            if (self.vokLogEq(g1, gt, pk_list[i]['pk1'], td_list[i]['td1'], td_list[i]['td2']) == False):
                    sys.exit("Error: trapdoors invalid")
        K = gt ** 0
        for td in td_list:
            K = K * td['td1']
        return K
        
    
n=10

print("Number of authorities:", n)

print("Initialisation :")
groupObj = PairingGroup('MNT159')
li = Like(groupObj)
print("Done")

print("Keys generation:")
(pk_O, sk_O) = li.keygen_u()
(pk_A, sk_A) = li.keygen_u()
(pk_B, sk_B) = li.keygen_u()
pk_aut = []
sk_aut = []
for i in range(n):
    (pk, sk) = li.keygen_a()
    pk_aut.append(pk)
    sk_aut.append(sk)
print("Done")

print("Precomputation:")
(h, w) = li.precomp(pk_aut, pk_A, pk_B)
print("Done")

print("Protocol:")
(x, X1, X2, pi_A) = li.A_step_1(w)
(y, Y, sigma_B_1, pi_B) = li.B_step_1(sk_B, pk_B, w, X1, X2, pi_A)
sigma_A = li.A_step_2(sk_A, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1)
sigma_B_2 = li.B_step_2(sk_B, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A)
K_A = li.A_out(h, x, Y)
K_B = li.B_out(h, y, X2) 
sigma_O = li.O_out(sk_O, pk_O, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A, sigma_B_2)
print("Done")

print("Check that Alice and Bob share the same key:", K_A == K_B)

print("Operator state verification:")
li.sst_verif(pk_aut, pk_O, pk_A, pk_B, w, X1, X2, Y, pi_A, pi_B, sigma_B_1, sigma_A, sigma_B_2, sigma_O)
print("Done")

print("Trapdoors generation:")
td = []
for i in range(n):
    td_ = li.td_gen(sk_aut[i], pk_aut[i], X1, Y)
    td.append(td_)
print("Done")

print("Key extraction:")
K_e = li.key_extract(td, pk_aut, X1, Y)
print("Done")

print("Check that the extracted key is correct:", K_A == K_e)
print("Program termination: success")
