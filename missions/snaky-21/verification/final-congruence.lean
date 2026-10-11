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
  have hL_32 : ([] : List Card) = [] := rfl
  have hL_31 : [placed 6 (15, 15) card_726] = [calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2330_eq hL_32
  have hL_30 : [placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2329_eq hL_31
  have hL_29 : [placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2328_eq hL_30
  have hL_28 : [placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2327_eq hL_29
  have hL_27 : [placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2326_eq hL_28
  have hL_26 : [placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2325_eq hL_27
  have hL_25 : [placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2324_eq hL_26
  have hL_24 : [placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2323_eq hL_25
  have hL_23 : [placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2322_eq hL_24
  have hL_22 : [placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2321_eq hL_23
  have hL_21 : [placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2320_eq hL_22
  have hL_20 : [placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2319_eq hL_21
  have hL_19 : [placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2318_eq hL_20
  have hL_18 : [placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2317_eq hL_19
  have hL_17 : [placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2316_eq hL_18
  have hL_16 : [placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2315_eq hL_17
  have hL_15 : [placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2314_eq hL_16
  have hL_14 : [placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2313_eq hL_15
  have hL_13 : [placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2312_eq hL_14
  have hL_12 : [placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2311_eq hL_13
  have hL_11 : [placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2310_eq hL_12
  have hL_10 : [placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2309_eq hL_11
  have hL_9 : [placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2308_eq hL_10
  have hL_8 : [placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2307_eq hL_9
  have hL_7 : [placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2306_eq hL_8
  have hL_6 : [placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2305_eq hL_7
  have hL_5 : [placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2304_eq hL_6
  have hL_4 : [placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2303_eq hL_5
  have hL_3 : [placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2302_eq hL_4
  have hL_2 : [placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2301_eq hL_3
  have hL_1 : [placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2300_eq hL_2
  have hL_0 : [placed 0 (4, 3) card_648, placed 1 (3, 4) card_648, placed 5 (3, 12) card_648, placed 2 (4, 13) card_648, placed 1 (0, 0) card_708, placed 4 (16, 0) card_708, placed 2 (0, 16) card_708, placed 7 (16, 16) card_708, placed 0 (3, 3) card_712, placed 1 (3, 3) card_712, placed 4 (13, 3) card_712, placed 5 (3, 13) card_712, placed 2 (3, 13) card_712, placed 3 (13, 3) card_712, placed 6 (13, 13) card_712, placed 7 (13, 13) card_712, placed 4 (13, 3) card_713, placed 5 (3, 13) card_713, placed 2 (3, 13) card_713, placed 3 (13, 3) card_713, placed 0 (1, 1) card_725, placed 1 (1, 1) card_725, placed 4 (15, 1) card_725, placed 5 (1, 15) card_725, placed 2 (1, 15) card_725, placed 3 (15, 1) card_725, placed 6 (15, 15) card_725, placed 7 (15, 15) card_725, placed 1 (1, 1) card_726, placed 4 (15, 1) card_726, placed 2 (1, 15) card_726, placed 6 (15, 15) card_726] = [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] :=
    congrArg₂ List.cons calc11_card_2299_eq hL_1
  have hA_31 : unionRequired [calc11_card_2330] = calc11_set_2331 :=
    calc11_set_2331_eq
  have hA_30 : unionRequired [calc11_card_2329, calc11_card_2330] = calc11_set_2333 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.required ∪ s) hA_31).trans calc11_set_2333_eq
  have hA_29 : unionRequired [calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2335 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.required ∪ s) hA_30).trans calc11_set_2335_eq
  have hA_28 : unionRequired [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2337 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.required ∪ s) hA_29).trans calc11_set_2337_eq
  have hA_27 : unionRequired [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2339 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.required ∪ s) hA_28).trans calc11_set_2339_eq
  have hA_26 : unionRequired [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2341 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.required ∪ s) hA_27).trans calc11_set_2341_eq
  have hA_25 : unionRequired [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2343 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.required ∪ s) hA_26).trans calc11_set_2343_eq
  have hA_24 : unionRequired [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2345 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.required ∪ s) hA_25).trans calc11_set_2345_eq
  have hA_23 : unionRequired [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2347 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.required ∪ s) hA_24).trans calc11_set_2347_eq
  have hA_22 : unionRequired [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2349 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.required ∪ s) hA_23).trans calc11_set_2349_eq
  have hA_21 : unionRequired [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2351 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.required ∪ s) hA_22).trans calc11_set_2351_eq
  have hA_20 : unionRequired [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2353 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.required ∪ s) hA_21).trans calc11_set_2353_eq
  have hA_19 : unionRequired [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2355 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.required ∪ s) hA_20).trans calc11_set_2355_eq
  have hA_18 : unionRequired [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2357 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.required ∪ s) hA_19).trans calc11_set_2357_eq
  have hA_17 : unionRequired [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2359 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.required ∪ s) hA_18).trans calc11_set_2359_eq
  have hA_16 : unionRequired [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2361 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.required ∪ s) hA_17).trans calc11_set_2361_eq
  have hA_15 : unionRequired [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2363 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.required ∪ s) hA_16).trans calc11_set_2363_eq
  have hA_14 : unionRequired [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2365 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.required ∪ s) hA_15).trans calc11_set_2365_eq
  have hA_13 : unionRequired [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2367 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.required ∪ s) hA_14).trans calc11_set_2367_eq
  have hA_12 : unionRequired [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2369 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.required ∪ s) hA_13).trans calc11_set_2369_eq
  have hA_11 : unionRequired [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2371 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.required ∪ s) hA_12).trans calc11_set_2371_eq
  have hA_10 : unionRequired [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2373 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.required ∪ s) hA_11).trans calc11_set_2373_eq
  have hA_9 : unionRequired [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2375 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.required ∪ s) hA_10).trans calc11_set_2375_eq
  have hA_8 : unionRequired [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2377 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.required ∪ s) hA_9).trans calc11_set_2377_eq
  have hA_7 : unionRequired [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2379 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.required ∪ s) hA_8).trans calc11_set_2379_eq
  have hA_6 : unionRequired [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2381 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.required ∪ s) hA_7).trans calc11_set_2381_eq
  have hA_5 : unionRequired [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2383 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.required ∪ s) hA_6).trans calc11_set_2383_eq
  have hA_4 : unionRequired [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2385 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.required ∪ s) hA_5).trans calc11_set_2385_eq
  have hA_3 : unionRequired [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2387 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.required ∪ s) hA_4).trans calc11_set_2387_eq
  have hA_2 : unionRequired [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2389 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.required ∪ s) hA_3).trans calc11_set_2389_eq
  have hA_1 : unionRequired [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2391 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.required ∪ s) hA_2).trans calc11_set_2391_eq
  have hA_0 : unionRequired [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2393 :=
    (congrArg (fun s : Finset Cell => calc11_card_2299.required ∪ s) hA_1).trans calc11_set_2393_eq
  have hT_31 : unionEnvelope [calc11_card_2330] = calc11_set_2332 :=
    calc11_set_2332_eq
  have hT_30 : unionEnvelope [calc11_card_2329, calc11_card_2330] = calc11_set_2334 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.envelope ∪ s) hT_31).trans calc11_set_2334_eq
  have hT_29 : unionEnvelope [calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2336 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.envelope ∪ s) hT_30).trans calc11_set_2336_eq
  have hT_28 : unionEnvelope [calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2338 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.envelope ∪ s) hT_29).trans calc11_set_2338_eq
  have hT_27 : unionEnvelope [calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2340 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.envelope ∪ s) hT_28).trans calc11_set_2340_eq
  have hT_26 : unionEnvelope [calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2342 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.envelope ∪ s) hT_27).trans calc11_set_2342_eq
  have hT_25 : unionEnvelope [calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2344 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.envelope ∪ s) hT_26).trans calc11_set_2344_eq
  have hT_24 : unionEnvelope [calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2346 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.envelope ∪ s) hT_25).trans calc11_set_2346_eq
  have hT_23 : unionEnvelope [calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2348 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.envelope ∪ s) hT_24).trans calc11_set_2348_eq
  have hT_22 : unionEnvelope [calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2350 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.envelope ∪ s) hT_23).trans calc11_set_2350_eq
  have hT_21 : unionEnvelope [calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2352 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.envelope ∪ s) hT_22).trans calc11_set_2352_eq
  have hT_20 : unionEnvelope [calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2354 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.envelope ∪ s) hT_21).trans calc11_set_2354_eq
  have hT_19 : unionEnvelope [calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2356 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.envelope ∪ s) hT_20).trans calc11_set_2356_eq
  have hT_18 : unionEnvelope [calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2358 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.envelope ∪ s) hT_19).trans calc11_set_2358_eq
  have hT_17 : unionEnvelope [calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2360 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.envelope ∪ s) hT_18).trans calc11_set_2360_eq
  have hT_16 : unionEnvelope [calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2362 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.envelope ∪ s) hT_17).trans calc11_set_2362_eq
  have hT_15 : unionEnvelope [calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2364 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.envelope ∪ s) hT_16).trans calc11_set_2364_eq
  have hT_14 : unionEnvelope [calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2366 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.envelope ∪ s) hT_15).trans calc11_set_2366_eq
  have hT_13 : unionEnvelope [calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2368 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.envelope ∪ s) hT_14).trans calc11_set_2368_eq
  have hT_12 : unionEnvelope [calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2370 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.envelope ∪ s) hT_13).trans calc11_set_2370_eq
  have hT_11 : unionEnvelope [calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2372 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.envelope ∪ s) hT_12).trans calc11_set_2372_eq
  have hT_10 : unionEnvelope [calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2374 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.envelope ∪ s) hT_11).trans calc11_set_2374_eq
  have hT_9 : unionEnvelope [calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2376 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.envelope ∪ s) hT_10).trans calc11_set_2376_eq
  have hT_8 : unionEnvelope [calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2378 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.envelope ∪ s) hT_9).trans calc11_set_2378_eq
  have hT_7 : unionEnvelope [calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2380 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.envelope ∪ s) hT_8).trans calc11_set_2380_eq
  have hT_6 : unionEnvelope [calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2382 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.envelope ∪ s) hT_7).trans calc11_set_2382_eq
  have hT_5 : unionEnvelope [calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2384 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.envelope ∪ s) hT_6).trans calc11_set_2384_eq
  have hT_4 : unionEnvelope [calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2386 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.envelope ∪ s) hT_5).trans calc11_set_2386_eq
  have hT_3 : unionEnvelope [calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2388 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.envelope ∪ s) hT_4).trans calc11_set_2388_eq
  have hT_2 : unionEnvelope [calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2390 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.envelope ∪ s) hT_3).trans calc11_set_2390_eq
  have hT_1 : unionEnvelope [calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2392 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.envelope ∪ s) hT_2).trans calc11_set_2392_eq
  have hT_0 : unionEnvelope [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2394 :=
    (congrArg (fun s : Finset Cell => calc11_card_2299.envelope ∪ s) hT_1).trans calc11_set_2394_eq
  have hI_31 : commonEnvelope [calc11_card_2299, calc11_card_2330] = calc11_set_2395 :=
    calc11_set_2395_eq
  have hI_30 : commonEnvelope [calc11_card_2299, calc11_card_2329, calc11_card_2330] = calc11_set_2396 :=
    (congrArg (fun s : Finset Cell => calc11_card_2329.envelope ∩ s) hI_31).trans calc11_set_2396_eq
  have hI_29 : commonEnvelope [calc11_card_2299, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2397 :=
    (congrArg (fun s : Finset Cell => calc11_card_2328.envelope ∩ s) hI_30).trans calc11_set_2397_eq
  have hI_28 : commonEnvelope [calc11_card_2299, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2398 :=
    (congrArg (fun s : Finset Cell => calc11_card_2327.envelope ∩ s) hI_29).trans calc11_set_2398_eq
  have hI_27 : commonEnvelope [calc11_card_2299, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2399 :=
    (congrArg (fun s : Finset Cell => calc11_card_2326.envelope ∩ s) hI_28).trans calc11_set_2399_eq
  have hI_26 : commonEnvelope [calc11_card_2299, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2400 :=
    (congrArg (fun s : Finset Cell => calc11_card_2325.envelope ∩ s) hI_27).trans calc11_set_2400_eq
  have hI_25 : commonEnvelope [calc11_card_2299, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2401 :=
    (congrArg (fun s : Finset Cell => calc11_card_2324.envelope ∩ s) hI_26).trans calc11_set_2401_eq
  have hI_24 : commonEnvelope [calc11_card_2299, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2402 :=
    (congrArg (fun s : Finset Cell => calc11_card_2323.envelope ∩ s) hI_25).trans calc11_set_2402_eq
  have hI_23 : commonEnvelope [calc11_card_2299, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2403 :=
    (congrArg (fun s : Finset Cell => calc11_card_2322.envelope ∩ s) hI_24).trans calc11_set_2403_eq
  have hI_22 : commonEnvelope [calc11_card_2299, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2404 :=
    (congrArg (fun s : Finset Cell => calc11_card_2321.envelope ∩ s) hI_23).trans calc11_set_2404_eq
  have hI_21 : commonEnvelope [calc11_card_2299, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2405 :=
    (congrArg (fun s : Finset Cell => calc11_card_2320.envelope ∩ s) hI_22).trans calc11_set_2405_eq
  have hI_20 : commonEnvelope [calc11_card_2299, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2406 :=
    (congrArg (fun s : Finset Cell => calc11_card_2319.envelope ∩ s) hI_21).trans calc11_set_2406_eq
  have hI_19 : commonEnvelope [calc11_card_2299, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2407 :=
    (congrArg (fun s : Finset Cell => calc11_card_2318.envelope ∩ s) hI_20).trans calc11_set_2407_eq
  have hI_18 : commonEnvelope [calc11_card_2299, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2408 :=
    (congrArg (fun s : Finset Cell => calc11_card_2317.envelope ∩ s) hI_19).trans calc11_set_2408_eq
  have hI_17 : commonEnvelope [calc11_card_2299, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2409 :=
    (congrArg (fun s : Finset Cell => calc11_card_2316.envelope ∩ s) hI_18).trans calc11_set_2409_eq
  have hI_16 : commonEnvelope [calc11_card_2299, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2410 :=
    (congrArg (fun s : Finset Cell => calc11_card_2315.envelope ∩ s) hI_17).trans calc11_set_2410_eq
  have hI_15 : commonEnvelope [calc11_card_2299, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2411 :=
    (congrArg (fun s : Finset Cell => calc11_card_2314.envelope ∩ s) hI_16).trans calc11_set_2411_eq
  have hI_14 : commonEnvelope [calc11_card_2299, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2412 :=
    (congrArg (fun s : Finset Cell => calc11_card_2313.envelope ∩ s) hI_15).trans calc11_set_2412_eq
  have hI_13 : commonEnvelope [calc11_card_2299, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2413 :=
    (congrArg (fun s : Finset Cell => calc11_card_2312.envelope ∩ s) hI_14).trans calc11_set_2413_eq
  have hI_12 : commonEnvelope [calc11_card_2299, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2414 :=
    (congrArg (fun s : Finset Cell => calc11_card_2311.envelope ∩ s) hI_13).trans calc11_set_2414_eq
  have hI_11 : commonEnvelope [calc11_card_2299, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2415 :=
    (congrArg (fun s : Finset Cell => calc11_card_2310.envelope ∩ s) hI_12).trans calc11_set_2415_eq
  have hI_10 : commonEnvelope [calc11_card_2299, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2416 :=
    (congrArg (fun s : Finset Cell => calc11_card_2309.envelope ∩ s) hI_11).trans calc11_set_2416_eq
  have hI_9 : commonEnvelope [calc11_card_2299, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2417 :=
    (congrArg (fun s : Finset Cell => calc11_card_2308.envelope ∩ s) hI_10).trans calc11_set_2417_eq
  have hI_8 : commonEnvelope [calc11_card_2299, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2418 :=
    (congrArg (fun s : Finset Cell => calc11_card_2307.envelope ∩ s) hI_9).trans calc11_set_2418_eq
  have hI_7 : commonEnvelope [calc11_card_2299, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2419 :=
    (congrArg (fun s : Finset Cell => calc11_card_2306.envelope ∩ s) hI_8).trans calc11_set_2419_eq
  have hI_6 : commonEnvelope [calc11_card_2299, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2420 :=
    (congrArg (fun s : Finset Cell => calc11_card_2305.envelope ∩ s) hI_7).trans calc11_set_2420_eq
  have hI_5 : commonEnvelope [calc11_card_2299, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2421 :=
    (congrArg (fun s : Finset Cell => calc11_card_2304.envelope ∩ s) hI_6).trans calc11_set_2421_eq
  have hI_4 : commonEnvelope [calc11_card_2299, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2422 :=
    (congrArg (fun s : Finset Cell => calc11_card_2303.envelope ∩ s) hI_5).trans calc11_set_2422_eq
  have hI_3 : commonEnvelope [calc11_card_2299, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2423 :=
    (congrArg (fun s : Finset Cell => calc11_card_2302.envelope ∩ s) hI_4).trans calc11_set_2423_eq
  have hI_2 : commonEnvelope [calc11_card_2299, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2424 :=
    (congrArg (fun s : Finset Cell => calc11_card_2301.envelope ∩ s) hI_3).trans calc11_set_2424_eq
  have hI_1 : commonEnvelope [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] = calc11_set_2425 :=
    (congrArg (fun s : Finset Cell => calc11_card_2300.envelope ∩ s) hI_2).trans calc11_set_2425_eq
  have hC : card_727 = combine (8, 8) [calc11_card_2299, calc11_card_2300, calc11_card_2301, calc11_card_2302, calc11_card_2303, calc11_card_2304, calc11_card_2305, calc11_card_2306, calc11_card_2307, calc11_card_2308, calc11_card_2309, calc11_card_2310, calc11_card_2311, calc11_card_2312, calc11_card_2313, calc11_card_2314, calc11_card_2315, calc11_card_2316, calc11_card_2317, calc11_card_2318, calc11_card_2319, calc11_card_2320, calc11_card_2321, calc11_card_2322, calc11_card_2323, calc11_card_2324, calc11_card_2325, calc11_card_2326, calc11_card_2327, calc11_card_2328, calc11_card_2329, calc11_card_2330] := by
    apply computed_card_ext
    · exact ((congrArg (fun s : Finset Cell => s.erase (8, 8))
        ((congrArg₂ (fun a b : Finset Cell => a ∪ b) hA_0 hI_1).trans calc11_set_2426_eq)).trans calc11_finishA_2427).symm
    · exact ((congrArg (fun s : Finset Cell => insert (8, 8) s) hT_0).trans calc11_finishT_2427).symm
    · decide +kernel
  exact hC.trans (congrArg (combine (8, 8)) hL_0).symm

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

#print axioms OAI.Snaky21.Certificate.valid_727
