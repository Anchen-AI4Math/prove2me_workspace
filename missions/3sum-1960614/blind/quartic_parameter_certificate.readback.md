# Read-back of `ThreeSum1960614.quartic_parameter_certificate`

readback_model: GPT-6

This is an unconditional assertion about fixed real numbers, with no hypotheses or free parameters. Write $H(x)=\bigl(-x\ln x-(1-x)\ln(1-x)\bigr)/\ln 2$ for binary entropy measured in bits; every argument of $H$ used below is strictly between $0$ and $1$. Define the real constants $A=116H(1/232)$ and $B=464H(1/464)-232H(1/232)-1$, and the real polynomial $P(x)=(785174904x+72447023x^2+24044466x^3+12022459x^4)/100000000$. The declaration asserts the conjunction of all eleven statements below (the rational number in the last statement is viewed as a real number):

$$
\begin{aligned}
(1)\quad &\frac{4648781151243719}{1000000000000000}<A,\\
(2)\quad &A<\frac{4648781151243720}{1000000000000000},\\
(3)\quad &\frac{1557987216578}{1000000000000000}<B,\\
(4)\quad &B<\frac{1557987216579}{1000000000000000},\\
(5)\quad &H\!\left(\frac{40409899}{1000000000}\right)<\frac{244168414687344}{1000000000000000},\\
(6)\quad &\frac{193175570}{1000000000}-2\left(-\frac{62656016}{1000000000}\right)<P\!\left(\frac{40409899}{1000000000}\right),\\
(7)\quad &\frac{\frac{193175570}{1000000000}-2\left(-\frac{62656016}{1000000000}\right)+\frac{13}{20}}{1-\frac{13}{20}}<P\!\left(\frac12\right),\\
(8)\quad &0<\frac{203889696}{1000000000}\left(A-\frac{62656016}{1000000000}\right),\\
(9)\quad &\frac{203889696}{1000000000}\left(A-\frac{62656016}{1000000000}\right)<1,\\
(10)\quad &\text{for every real }z\text{ occurring in the twelve-entry list }\mathcal L\text{ below, }z<\frac{196061388}{100000000},\\
(11)\quad &\frac{196061388}{100000000}<\frac{1960614}{1000000}.
\end{aligned}
$$

Here $\mathcal L$ is exactly the following ordered list of twelve real values, with every constant written as an exact fraction:

$$
\begin{aligned}
L_1&=2\frac{203889696}{1000000000}A,\\
L_2&=1+\frac{203889696}{1000000000}\left(A+\frac{62656016}{1000000000}\right),\\
L_3&=2-\frac{203889696}{1000000000}\frac{193175570}{1000000000},\\
L_4&=2-\frac{203889696}{1000000000}\left(\frac12-\frac{62656016}{1000000000}-H\!\left(\frac{40409899}{1000000000}\right)\right),\\
L_5&=2-\frac{203889696}{1000000000}\left(\frac12+\frac{62656016}{1000000000}-B-\frac{2790503}{10000000}\left(1+\frac{193175570}{1000000000}+2\frac{62656016}{1000000000}\right)\right),\\
L_6&=2-\frac{203889696}{1000000000}\left(\frac{13}{20}-\frac12+\frac{62656016}{1000000000}-B\right),\\
L_7&=\frac{203889696}{1000000000}\frac85\left(A+\frac12\right),\\
L_8&=2+\frac{203889696}{1000000000}\left(\frac45-\frac25A+2\frac{62656016}{1000000000}\right),\\
L_9&=1+\frac{203889696}{1000000000}\left(\frac12+\frac{62656016}{1000000000}\right),\\
L_{10}&=2-\frac{203889696}{1000000000}\left(A-\frac{62656016}{1000000000}\right),\\
L_{11}&=2-2\frac{203889696}{1000000000}\left(A-\frac{62656016}{1000000000}\right),\\
L_{12}&=1,
\qquad\mathcal L=(L_1,L_2,\ldots,L_{12}).
\end{aligned}
$$

The quantifier in (10) ranges over membership in this fixed list, so it asserts the strict bound for each of these twelve entries; the list is nonempty and includes the value $1$. All divisions here have nonzero denominators, including $1-13/20=7/20$ in (7), and none of the assertions is conditional on a choice of an input, a natural-number parameter, or an entropy argument.
