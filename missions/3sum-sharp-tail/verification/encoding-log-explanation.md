This certificate encloses the natural logarithms of 2, 10, 3, 9, 1/21 and 20/21 by the exact rational endpoints in the target statement. These are the constants needed for the encoding exponent, the baseline entropy H(1/21), and the denominator log(4).

For each normalized argument y in [1,2], set z=(y-1)/(y+1). The verified inequalities

$$2\sum_{i<K}\frac{z^{2i+1}}{2i+1}\le\log y\le
2\left(\sum_{i<K}\frac{z^{2i+1}}{2i+1}+\frac{z^{2K+1}}{1-z^2}\right)$$

reduce the enclosure to finite rational arithmetic. Here z is between zero and one third. We use K=16 for log(2), with z=1/3, and K=12 for the remaining normalized arguments.

The scaling identities use

$$10=2^3(5/4),\quad3=2(3/2),\quad9=2^3(9/8),$$
$$1/21=2^{-5}(32/21),\quad20/21=2^{-1}(40/21).$$

The logarithm product and power identities transfer the rational enclosures to the required constants. Both partial sums and remainder comparisons are exact; no floating-point approximation is used. This is a leaf proof with no open platform theorem dependency.
