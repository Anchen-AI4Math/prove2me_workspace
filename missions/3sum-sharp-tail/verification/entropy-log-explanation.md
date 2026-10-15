Put theta=5601/50000 and u=(1-theta)/21=44399/1050000. The certificate encloses the natural logarithms of u, 1-u, theta and 1-theta by the exact rational endpoints in the target statement. These are the four logarithms defining the sharp-tail and query entropy terms.

Power-of-two scaling puts the arguments in [1,2]:

$$2^5u=88798/65625,\quad2(1-u)=1005601/525000,$$
$$2^4\theta=5601/3125,\quad2(1-\theta)=44399/25000.$$

For each scaled argument y we apply the verified atanh-series lower and upper bounds at z=(y-1)/(y+1), with K=12 terms and the explicit positive rational remainder. The finite sums and error comparisons are checked exactly. The imported encoding logarithm certificate supplies the bounds for log(2); subtracting the appropriate multiple of log(2) gives the asserted intervals.

This proof therefore has the genuine platform dependency on the encoding logarithm certificate and makes no algorithmic assumption.
