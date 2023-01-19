#!/usr/bin/env sage

from estimator import *

n = 8192
q = 2**214-255
nike = LWE.Parameters(n=n,q=q,Xs=ND.SparseTernary(n,p=n/4,m=n/4),Xe=ND.SparseTernary(n,p=n/4,m=n/4))
print("\n# n = {}, q = {}".format(n, q)) 
LWE.estimate(nike.updated(m=n), jobs=4, deny_list = {"dual_mitm_hybrid", "dual_hybrid", "bkw"}, red_cost_model=RC.LaaMosPol14)
#lwe.arora_gb(nike)
LWE.coded_bkw(nike)
LWE.dual_hybrid(nike, mitm_optimization = True)
