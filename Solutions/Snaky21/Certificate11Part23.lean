import Definitions.Def_Snaky21Calc11
import Solutions.Snaky21.Geometry
import Solutions.Snaky21.Certificate11Part22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OAI.Snaky21.Certificate
open OAI.Snaky21 OAI.SnakyPrototype

theorem calc11_card_2299_eq : placed 0 (4, 3) card_648 = calc11_card_2299 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2300_eq : placed 1 (3, 4) card_648 = calc11_card_2300 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2301_eq : placed 5 (3, 12) card_648 = calc11_card_2301 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2302_eq : placed 2 (4, 13) card_648 = calc11_card_2302 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2303_eq : placed 1 (0, 0) card_708 = calc11_card_2303 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2304_eq : placed 4 (16, 0) card_708 = calc11_card_2304 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2305_eq : placed 2 (0, 16) card_708 = calc11_card_2305 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2306_eq : placed 7 (16, 16) card_708 = calc11_card_2306 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2307_eq : placed 0 (3, 3) card_712 = calc11_card_2307 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2308_eq : placed 1 (3, 3) card_712 = calc11_card_2308 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2309_eq : placed 4 (13, 3) card_712 = calc11_card_2309 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2310_eq : placed 5 (3, 13) card_712 = calc11_card_2310 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2311_eq : placed 2 (3, 13) card_712 = calc11_card_2311 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2312_eq : placed 3 (13, 3) card_712 = calc11_card_2312 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2313_eq : placed 6 (13, 13) card_712 = calc11_card_2313 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2314_eq : placed 7 (13, 13) card_712 = calc11_card_2314 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2315_eq : placed 4 (13, 3) card_713 = calc11_card_2315 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2316_eq : placed 5 (3, 13) card_713 = calc11_card_2316 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2317_eq : placed 2 (3, 13) card_713 = calc11_card_2317 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2318_eq : placed 3 (13, 3) card_713 = calc11_card_2318 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2319_eq : placed 0 (1, 1) card_725 = calc11_card_2319 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2320_eq : placed 1 (1, 1) card_725 = calc11_card_2320 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2321_eq : placed 4 (15, 1) card_725 = calc11_card_2321 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2322_eq : placed 5 (1, 15) card_725 = calc11_card_2322 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2323_eq : placed 2 (1, 15) card_725 = calc11_card_2323 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2324_eq : placed 3 (15, 1) card_725 = calc11_card_2324 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2325_eq : placed 6 (15, 15) card_725 = calc11_card_2325 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2326_eq : placed 7 (15, 15) card_725 = calc11_card_2326 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2327_eq : placed 1 (1, 1) card_726 = calc11_card_2327 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2328_eq : placed 4 (15, 1) card_726 = calc11_card_2328 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2329_eq : placed 2 (1, 15) card_726 = calc11_card_2329 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_card_2330_eq : placed 6 (15, 15) card_726 = calc11_card_2330 := by
  apply computed_card_ext <;> decide +kernel

theorem calc11_set_2331_eq : calc11_card_2330.required ∪ ∅ = calc11_set_2331 := by decide +kernel

theorem calc11_set_2332_eq : calc11_card_2330.envelope ∪ ∅ = calc11_set_2332 := by decide +kernel

theorem calc11_set_2333_eq : calc11_card_2329.required ∪ calc11_set_2331 = calc11_set_2333 := by decide +kernel

theorem calc11_set_2334_eq : calc11_card_2329.envelope ∪ calc11_set_2332 = calc11_set_2334 := by decide +kernel

theorem calc11_set_2335_eq : calc11_card_2328.required ∪ calc11_set_2333 = calc11_set_2335 := by decide +kernel

theorem calc11_set_2336_eq : calc11_card_2328.envelope ∪ calc11_set_2334 = calc11_set_2336 := by decide +kernel

theorem calc11_set_2337_eq : calc11_card_2327.required ∪ calc11_set_2335 = calc11_set_2337 := by decide +kernel

theorem calc11_set_2338_eq : calc11_card_2327.envelope ∪ calc11_set_2336 = calc11_set_2338 := by decide +kernel

theorem calc11_set_2339_eq : calc11_card_2326.required ∪ calc11_set_2337 = calc11_set_2339 := by decide +kernel

theorem calc11_set_2340_eq : calc11_card_2326.envelope ∪ calc11_set_2338 = calc11_set_2340 := by decide +kernel

theorem calc11_set_2341_eq : calc11_card_2325.required ∪ calc11_set_2339 = calc11_set_2341 := by decide +kernel

theorem calc11_set_2342_eq : calc11_card_2325.envelope ∪ calc11_set_2340 = calc11_set_2342 := by decide +kernel

theorem calc11_set_2343_eq : calc11_card_2324.required ∪ calc11_set_2341 = calc11_set_2343 := by decide +kernel

theorem calc11_set_2344_eq : calc11_card_2324.envelope ∪ calc11_set_2342 = calc11_set_2344 := by decide +kernel

theorem calc11_set_2345_eq : calc11_card_2323.required ∪ calc11_set_2343 = calc11_set_2345 := by decide +kernel

theorem calc11_set_2346_eq : calc11_card_2323.envelope ∪ calc11_set_2344 = calc11_set_2346 := by decide +kernel

theorem calc11_set_2347_eq : calc11_card_2322.required ∪ calc11_set_2345 = calc11_set_2347 := by decide +kernel

theorem calc11_set_2348_eq : calc11_card_2322.envelope ∪ calc11_set_2346 = calc11_set_2348 := by decide +kernel

theorem calc11_set_2349_eq : calc11_card_2321.required ∪ calc11_set_2347 = calc11_set_2349 := by decide +kernel

theorem calc11_set_2350_eq : calc11_card_2321.envelope ∪ calc11_set_2348 = calc11_set_2350 := by decide +kernel

theorem calc11_set_2351_eq : calc11_card_2320.required ∪ calc11_set_2349 = calc11_set_2351 := by decide +kernel

theorem calc11_set_2352_eq : calc11_card_2320.envelope ∪ calc11_set_2350 = calc11_set_2352 := by decide +kernel

theorem calc11_set_2353_eq : calc11_card_2319.required ∪ calc11_set_2351 = calc11_set_2353 := by decide +kernel

theorem calc11_set_2354_eq : calc11_card_2319.envelope ∪ calc11_set_2352 = calc11_set_2354 := by decide +kernel

theorem calc11_set_2355_eq : calc11_card_2318.required ∪ calc11_set_2353 = calc11_set_2355 := by decide +kernel

theorem calc11_set_2356_eq : calc11_card_2318.envelope ∪ calc11_set_2354 = calc11_set_2356 := by decide +kernel

theorem calc11_set_2357_eq : calc11_card_2317.required ∪ calc11_set_2355 = calc11_set_2357 := by decide +kernel

theorem calc11_set_2358_eq : calc11_card_2317.envelope ∪ calc11_set_2356 = calc11_set_2358 := by decide +kernel

theorem calc11_set_2359_eq : calc11_card_2316.required ∪ calc11_set_2357 = calc11_set_2359 := by decide +kernel

theorem calc11_set_2360_eq : calc11_card_2316.envelope ∪ calc11_set_2358 = calc11_set_2360 := by decide +kernel

theorem calc11_set_2361_eq : calc11_card_2315.required ∪ calc11_set_2359 = calc11_set_2361 := by decide +kernel

theorem calc11_set_2362_eq : calc11_card_2315.envelope ∪ calc11_set_2360 = calc11_set_2362 := by decide +kernel

theorem calc11_set_2363_eq : calc11_card_2314.required ∪ calc11_set_2361 = calc11_set_2363 := by decide +kernel

theorem calc11_set_2364_eq : calc11_card_2314.envelope ∪ calc11_set_2362 = calc11_set_2364 := by decide +kernel

theorem calc11_set_2365_eq : calc11_card_2313.required ∪ calc11_set_2363 = calc11_set_2365 := by decide +kernel

theorem calc11_set_2366_eq : calc11_card_2313.envelope ∪ calc11_set_2364 = calc11_set_2366 := by decide +kernel

theorem calc11_set_2367_eq : calc11_card_2312.required ∪ calc11_set_2365 = calc11_set_2367 := by decide +kernel

theorem calc11_set_2368_eq : calc11_card_2312.envelope ∪ calc11_set_2366 = calc11_set_2368 := by decide +kernel

theorem calc11_set_2369_eq : calc11_card_2311.required ∪ calc11_set_2367 = calc11_set_2369 := by decide +kernel

theorem calc11_set_2370_eq : calc11_card_2311.envelope ∪ calc11_set_2368 = calc11_set_2370 := by decide +kernel

theorem calc11_set_2371_eq : calc11_card_2310.required ∪ calc11_set_2369 = calc11_set_2371 := by decide +kernel

theorem calc11_set_2372_eq : calc11_card_2310.envelope ∪ calc11_set_2370 = calc11_set_2372 := by decide +kernel

theorem calc11_set_2373_eq : calc11_card_2309.required ∪ calc11_set_2371 = calc11_set_2373 := by decide +kernel

theorem calc11_set_2374_eq : calc11_card_2309.envelope ∪ calc11_set_2372 = calc11_set_2374 := by decide +kernel

theorem calc11_set_2375_eq : calc11_card_2308.required ∪ calc11_set_2373 = calc11_set_2375 := by decide +kernel

theorem calc11_set_2376_eq : calc11_card_2308.envelope ∪ calc11_set_2374 = calc11_set_2376 := by decide +kernel

theorem calc11_set_2377_eq : calc11_card_2307.required ∪ calc11_set_2375 = calc11_set_2377 := by decide +kernel

theorem calc11_set_2378_eq : calc11_card_2307.envelope ∪ calc11_set_2376 = calc11_set_2378 := by decide +kernel

theorem calc11_set_2379_eq : calc11_card_2306.required ∪ calc11_set_2377 = calc11_set_2379 := by decide +kernel

theorem calc11_set_2380_eq : calc11_card_2306.envelope ∪ calc11_set_2378 = calc11_set_2380 := by decide +kernel

theorem calc11_set_2381_eq : calc11_card_2305.required ∪ calc11_set_2379 = calc11_set_2381 := by decide +kernel

theorem calc11_set_2382_eq : calc11_card_2305.envelope ∪ calc11_set_2380 = calc11_set_2382 := by decide +kernel

theorem calc11_set_2383_eq : calc11_card_2304.required ∪ calc11_set_2381 = calc11_set_2383 := by decide +kernel

theorem calc11_set_2384_eq : calc11_card_2304.envelope ∪ calc11_set_2382 = calc11_set_2384 := by decide +kernel

theorem calc11_set_2385_eq : calc11_card_2303.required ∪ calc11_set_2383 = calc11_set_2385 := by decide +kernel

theorem calc11_set_2386_eq : calc11_card_2303.envelope ∪ calc11_set_2384 = calc11_set_2386 := by decide +kernel

theorem calc11_set_2387_eq : calc11_card_2302.required ∪ calc11_set_2385 = calc11_set_2387 := by decide +kernel

theorem calc11_set_2388_eq : calc11_card_2302.envelope ∪ calc11_set_2386 = calc11_set_2388 := by decide +kernel

theorem calc11_set_2389_eq : calc11_card_2301.required ∪ calc11_set_2387 = calc11_set_2389 := by decide +kernel

theorem calc11_set_2390_eq : calc11_card_2301.envelope ∪ calc11_set_2388 = calc11_set_2390 := by decide +kernel

theorem calc11_set_2391_eq : calc11_card_2300.required ∪ calc11_set_2389 = calc11_set_2391 := by decide +kernel

theorem calc11_set_2392_eq : calc11_card_2300.envelope ∪ calc11_set_2390 = calc11_set_2392 := by decide +kernel

theorem calc11_set_2393_eq : calc11_card_2299.required ∪ calc11_set_2391 = calc11_set_2393 := by decide +kernel

theorem calc11_set_2394_eq : calc11_card_2299.envelope ∪ calc11_set_2392 = calc11_set_2394 := by decide +kernel

theorem calc11_set_2395_eq : calc11_card_2330.envelope ∩ calc11_card_2299.envelope = calc11_set_2395 := by decide +kernel

theorem calc11_set_2396_eq : calc11_card_2329.envelope ∩ calc11_set_2395 = calc11_set_2396 := by decide +kernel

theorem calc11_set_2397_eq : calc11_card_2328.envelope ∩ calc11_set_2396 = calc11_set_2397 := by decide +kernel

theorem calc11_set_2398_eq : calc11_card_2327.envelope ∩ calc11_set_2397 = calc11_set_2398 := by decide +kernel

theorem calc11_set_2399_eq : calc11_card_2326.envelope ∩ calc11_set_2398 = calc11_set_2399 := by decide +kernel

theorem calc11_set_2400_eq : calc11_card_2325.envelope ∩ calc11_set_2399 = calc11_set_2400 := by decide +kernel

theorem calc11_set_2401_eq : calc11_card_2324.envelope ∩ calc11_set_2400 = calc11_set_2401 := by decide +kernel

theorem calc11_set_2402_eq : calc11_card_2323.envelope ∩ calc11_set_2401 = calc11_set_2402 := by decide +kernel

theorem calc11_set_2403_eq : calc11_card_2322.envelope ∩ calc11_set_2402 = calc11_set_2403 := by decide +kernel

theorem calc11_set_2404_eq : calc11_card_2321.envelope ∩ calc11_set_2403 = calc11_set_2404 := by decide +kernel

theorem calc11_set_2405_eq : calc11_card_2320.envelope ∩ calc11_set_2404 = calc11_set_2405 := by decide +kernel

theorem calc11_set_2406_eq : calc11_card_2319.envelope ∩ calc11_set_2405 = calc11_set_2406 := by decide +kernel

theorem calc11_set_2407_eq : calc11_card_2318.envelope ∩ calc11_set_2406 = calc11_set_2407 := by decide +kernel

theorem calc11_set_2408_eq : calc11_card_2317.envelope ∩ calc11_set_2407 = calc11_set_2408 := by decide +kernel

theorem calc11_set_2409_eq : calc11_card_2316.envelope ∩ calc11_set_2408 = calc11_set_2409 := by decide +kernel

theorem calc11_set_2410_eq : calc11_card_2315.envelope ∩ calc11_set_2409 = calc11_set_2410 := by decide +kernel

theorem calc11_set_2411_eq : calc11_card_2314.envelope ∩ calc11_set_2410 = calc11_set_2411 := by decide +kernel

theorem calc11_set_2412_eq : calc11_card_2313.envelope ∩ calc11_set_2411 = calc11_set_2412 := by decide +kernel

theorem calc11_set_2413_eq : calc11_card_2312.envelope ∩ calc11_set_2412 = calc11_set_2413 := by decide +kernel

theorem calc11_set_2414_eq : calc11_card_2311.envelope ∩ calc11_set_2413 = calc11_set_2414 := by decide +kernel

theorem calc11_set_2415_eq : calc11_card_2310.envelope ∩ calc11_set_2414 = calc11_set_2415 := by decide +kernel

theorem calc11_set_2416_eq : calc11_card_2309.envelope ∩ calc11_set_2415 = calc11_set_2416 := by decide +kernel

theorem calc11_set_2417_eq : calc11_card_2308.envelope ∩ calc11_set_2416 = calc11_set_2417 := by decide +kernel

theorem calc11_set_2418_eq : calc11_card_2307.envelope ∩ calc11_set_2417 = calc11_set_2418 := by decide +kernel

theorem calc11_set_2419_eq : calc11_card_2306.envelope ∩ calc11_set_2418 = calc11_set_2419 := by decide +kernel

theorem calc11_set_2420_eq : calc11_card_2305.envelope ∩ calc11_set_2419 = calc11_set_2420 := by decide +kernel

theorem calc11_set_2421_eq : calc11_card_2304.envelope ∩ calc11_set_2420 = calc11_set_2421 := by decide +kernel

theorem calc11_set_2422_eq : calc11_card_2303.envelope ∩ calc11_set_2421 = calc11_set_2422 := by decide +kernel

theorem calc11_set_2423_eq : calc11_card_2302.envelope ∩ calc11_set_2422 = calc11_set_2423 := by decide +kernel

theorem calc11_set_2424_eq : calc11_card_2301.envelope ∩ calc11_set_2423 = calc11_set_2424 := by decide +kernel

theorem calc11_set_2425_eq : calc11_card_2300.envelope ∩ calc11_set_2424 = calc11_set_2425 := by decide +kernel

theorem calc11_set_2426_eq : calc11_set_2393 ∪ calc11_set_2425 = calc11_set_2426 := by decide +kernel

theorem calc11_finishA_2427 : calc11_set_2426.erase (8, 8) = card_727.required := by decide +kernel

theorem calc11_finishT_2427 : insert (8, 8) calc11_set_2394 = card_727.envelope := by decide +kernel

theorem eq_card_727 : card_727 = combine (8, 8) [placed 0 (4, 3) card_648, placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] := by
  rw [calc11_card_2299_eq, calc11_card_2300_eq, calc11_card_2301_eq, calc11_card_2302_eq, calc11_card_2303_eq, calc11_card_2304_eq, calc11_card_2305_eq, calc11_card_2306_eq, calc11_card_2307_eq, calc11_card_2308_eq, calc11_card_2309_eq, calc11_card_2310_eq, calc11_card_2311_eq, calc11_card_2312_eq, calc11_card_2313_eq, calc11_card_2314_eq, calc11_card_2315_eq, calc11_card_2316_eq, calc11_card_2317_eq, calc11_card_2318_eq, calc11_card_2319_eq, calc11_card_2320_eq, calc11_card_2321_eq, calc11_card_2322_eq, calc11_card_2323_eq, calc11_card_2324_eq, calc11_card_2325_eq, calc11_card_2326_eq, calc11_card_2327_eq, calc11_card_2328_eq, calc11_card_2329_eq, calc11_card_2330_eq]
  apply computed_card_ext
  · simp only [combine, unionRequired, commonEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2331_eq, calc11_set_2333_eq, calc11_set_2335_eq, calc11_set_2337_eq, calc11_set_2339_eq, calc11_set_2341_eq, calc11_set_2343_eq, calc11_set_2345_eq, calc11_set_2347_eq, calc11_set_2349_eq, calc11_set_2351_eq, calc11_set_2353_eq, calc11_set_2355_eq, calc11_set_2357_eq, calc11_set_2359_eq, calc11_set_2361_eq, calc11_set_2363_eq, calc11_set_2365_eq, calc11_set_2367_eq, calc11_set_2369_eq, calc11_set_2371_eq, calc11_set_2373_eq, calc11_set_2375_eq, calc11_set_2377_eq, calc11_set_2379_eq, calc11_set_2381_eq, calc11_set_2383_eq, calc11_set_2385_eq, calc11_set_2387_eq, calc11_set_2389_eq, calc11_set_2391_eq, calc11_set_2393_eq, calc11_set_2395_eq, calc11_set_2396_eq, calc11_set_2397_eq, calc11_set_2398_eq, calc11_set_2399_eq, calc11_set_2400_eq, calc11_set_2401_eq, calc11_set_2402_eq, calc11_set_2403_eq, calc11_set_2404_eq, calc11_set_2405_eq, calc11_set_2406_eq, calc11_set_2407_eq, calc11_set_2408_eq, calc11_set_2409_eq, calc11_set_2410_eq, calc11_set_2411_eq, calc11_set_2412_eq, calc11_set_2413_eq, calc11_set_2414_eq, calc11_set_2415_eq, calc11_set_2416_eq, calc11_set_2417_eq, calc11_set_2418_eq, calc11_set_2419_eq, calc11_set_2420_eq, calc11_set_2421_eq, calc11_set_2422_eq, calc11_set_2423_eq, calc11_set_2424_eq, calc11_set_2425_eq, calc11_set_2426_eq, calc11_finishA_2427]
  · simp only [combine, unionEnvelope, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [calc11_set_2332_eq, calc11_set_2334_eq, calc11_set_2336_eq, calc11_set_2338_eq, calc11_set_2340_eq, calc11_set_2342_eq, calc11_set_2344_eq, calc11_set_2346_eq, calc11_set_2348_eq, calc11_set_2350_eq, calc11_set_2352_eq, calc11_set_2354_eq, calc11_set_2356_eq, calc11_set_2358_eq, calc11_set_2360_eq, calc11_set_2362_eq, calc11_set_2364_eq, calc11_set_2366_eq, calc11_set_2368_eq, calc11_set_2370_eq, calc11_set_2372_eq, calc11_set_2374_eq, calc11_set_2376_eq, calc11_set_2378_eq, calc11_set_2380_eq, calc11_set_2382_eq, calc11_set_2384_eq, calc11_set_2386_eq, calc11_set_2388_eq, calc11_set_2390_eq, calc11_set_2392_eq, calc11_set_2394_eq, calc11_finishT_2427]
  · decide +kernel

theorem valid_727 : Valid card_727 := by
  rw [eq_card_727]
  apply combination_rule (8, 8) _ (by simp)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | hc
  · exact placed_valid 0 (4, 3) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 4) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 12) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 2 (4, 13) valid_648
  rcases hc with rfl | hc
  · exact placed_valid 1 (0, 0) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 4 (16, 0) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 2 (0, 16) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 7 (16, 16) valid_708
  rcases hc with rfl | hc
  · exact placed_valid 0 (3, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 1 (3, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 6 (13, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 7 (13, 13) valid_712
  rcases hc with rfl | hc
  · exact placed_valid 4 (13, 3) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 5 (3, 13) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 2 (3, 13) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 3 (13, 3) valid_713
  rcases hc with rfl | hc
  · exact placed_valid 0 (1, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 4 (15, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 5 (1, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 3 (15, 1) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 6 (15, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 7 (15, 15) valid_725
  rcases hc with rfl | hc
  · exact placed_valid 1 (1, 1) valid_726
  rcases hc with rfl | hc
  · exact placed_valid 4 (15, 1) valid_726
  rcases hc with rfl | hc
  · exact placed_valid 2 (1, 15) valid_726
  subst c
  exact placed_valid 6 (15, 15) valid_726


end OAI.Snaky21.Certificate
