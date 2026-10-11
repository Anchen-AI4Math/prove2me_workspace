import sys
sys.path.insert(0, r"D:/users/self_projects/prove2me_workspace/tmp/zeta7/exact_packages")
from mpmath import mp, mpf, pi, sin, cos, exp, factorial

mp.dps = 50

def K7_direct(z, N=400):
    s = mpf(0)
    for k in range(-N, N + 1):
        s += (z - k) ** (-7)
    return s

def K7_trig(z):
    return pi**7 * (302*cos(pi*z) + 57*cos(3*pi*z) + cos(5*pi*z)) / (360 * sin(pi*z)**7)

def K7_eulerian(z):
    q = exp(2*pi*1j*z)
    num = q*(1 + 57*q + 302*q**2 + 302*q**3 + 57*q**4 + q**5)
    return 1j * (2*pi)**7 / 720 * num / (1 - q)**7

print("Eulerian numerator coefficient sum:", 1+57+302+302+57+1, " 6! =", int(factorial(6)))
print("trig-form numerator coefficient sum:", 302+57+1)

for z in [mpf("0.37") + mpf("0.8")*1j, mpf("2.5") + mpf("0.05")*1j]:
    d = K7_direct(z)
    t = K7_trig(z)
    e = K7_eulerian(z)
    print(f"z={z}")
    print("  |direct - trig|     =", abs(d - t))
    print("  |direct - eulerian| =", abs(d - e))

# check the K7 derivative definition: K7 = (1/6!) d^6/dz^6 (pi cot pi z)
from mpmath import cot, diff
z = mpf("0.37") + mpf("0.8")*1j
deriv = diff(lambda w: pi*cot(pi*w), z, 6) / factorial(6)
print("derivative def vs direct:", abs(deriv - K7_direct(z)))

# f_* margin check
tau = mpf(2641)/250
fstar = mpf("-10.5641538376402")
print("tau =", tau, " -f_* =", -fstar, " margin -f_* - tau =", -fstar - tau)
print("f_* < -tau ?", fstar < -tau)
