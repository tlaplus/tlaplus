/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class DetlefsTest extends PCalModelCheckerTestCase {

	public DetlefsTest() {
		super("Detlefs", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2127012", "952912", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "82"));
		
		assertCoverage("  line 309, col 27 to line 309, col 84 of module Detlefs: 3588\n" + 
				"  line 310, col 27 to line 310, col 61 of module Detlefs: 3588\n" + 
				"  line 311, col 27 to line 311, col 60 of module Detlefs: 7382\n" + 
				"  line 312, col 37 to line 312, col 44 of module Detlefs: 7382\n" + 
				"  line 314, col 27 to line 314, col 64 of module Detlefs: 7382\n" + 
				"  line 315, col 27 to line 315, col 59 of module Detlefs: 7382\n" + 
				"  line 316, col 27 to line 316, col 59 of module Detlefs: 3588\n" + 
				"  line 317, col 27 to line 317, col 38 of module Detlefs: 3588\n" + 
				"  line 318, col 26 to line 321, col 54 of module Detlefs: 0\n" + 
				"  line 324, col 17 to line 324, col 64 of module Detlefs: 3586\n" + 
				"  line 325, col 17 to line 325, col 67 of module Detlefs: 3586\n" + 
				"  line 326, col 17 to line 326, col 67 of module Detlefs: 3586\n" + 
				"  line 327, col 17 to line 327, col 67 of module Detlefs: 3586\n" + 
				"  line 328, col 17 to line 328, col 67 of module Detlefs: 3586\n" + 
				"  line 329, col 17 to line 329, col 73 of module Detlefs: 3586\n" + 
				"  line 330, col 17 to line 330, col 64 of module Detlefs: 3586\n" + 
				"  line 331, col 17 to line 331, col 67 of module Detlefs: 3586\n" + 
				"  line 332, col 27 to line 335, col 41 of module Detlefs: 0\n" + 
				"  line 338, col 17 to line 339, col 61 of module Detlefs: 3669\n" + 
				"  line 340, col 17 to line 340, col 48 of module Detlefs: 3669\n" + 
				"  line 341, col 27 to line 344, col 77 of module Detlefs: 0\n" + 
				"  line 347, col 16 to line 347, col 53 of module Detlefs: 6356\n" + 
				"  line 348, col 16 to line 348, col 47 of module Detlefs: 6356\n" + 
				"  line 349, col 26 to line 352, col 67 of module Detlefs: 0\n" + 
				"  line 355, col 16 to line 355, col 61 of module Detlefs: 8708\n" + 
				"  line 356, col 16 to line 356, col 47 of module Detlefs: 8708\n" + 
				"  line 357, col 26 to line 360, col 67 of module Detlefs: 0\n" + 
				"  line 364, col 27 to line 364, col 68 of module Detlefs: 3382\n" + 
				"  line 365, col 27 to line 365, col 63 of module Detlefs: 3382\n" + 
				"  line 366, col 27 to line 366, col 58 of module Detlefs: 3382\n" + 
				"  line 367, col 27 to line 367, col 58 of module Detlefs: 4995\n" + 
				"  line 368, col 37 to line 368, col 50 of module Detlefs: 0\n" + 
				"  line 369, col 26 to line 372, col 59 of module Detlefs: 0\n" + 
				"  line 377, col 30 to line 377, col 49 of module Detlefs: 1914\n" + 
				"  line 378, col 30 to line 378, col 50 of module Detlefs: 1914\n" + 
				"  line 379, col 27 to line 379, col 64 of module Detlefs: 1914\n" + 
				"  line 380, col 27 to line 380, col 65 of module Detlefs: 1428\n" + 
				"  line 381, col 37 to line 381, col 59 of module Detlefs: 0\n" + 
				"  line 383, col 27 to line 383, col 64 of module Detlefs: 1914\n" + 
				"  line 384, col 27 to line 384, col 59 of module Detlefs: 1914\n" + 
				"  line 385, col 27 to line 385, col 58 of module Detlefs: 1428\n" + 
				"  line 386, col 27 to line 386, col 38 of module Detlefs: 1428\n" + 
				"  line 387, col 26 to line 390, col 48 of module Detlefs: 0\n" + 
				"  line 393, col 17 to line 393, col 64 of module Detlefs: 2860\n" + 
				"  line 394, col 17 to line 394, col 67 of module Detlefs: 2860\n" + 
				"  line 395, col 17 to line 395, col 67 of module Detlefs: 2860\n" + 
				"  line 396, col 17 to line 396, col 67 of module Detlefs: 2860\n" + 
				"  line 397, col 17 to line 397, col 67 of module Detlefs: 2860\n" + 
				"  line 398, col 17 to line 398, col 73 of module Detlefs: 2860\n" + 
				"  line 399, col 17 to line 399, col 64 of module Detlefs: 2860\n" + 
				"  line 400, col 17 to line 400, col 67 of module Detlefs: 2860\n" + 
				"  line 401, col 27 to line 404, col 41 of module Detlefs: 0\n" + 
				"  line 407, col 16 to line 407, col 61 of module Detlefs: 4670\n" + 
				"  line 408, col 16 to line 408, col 47 of module Detlefs: 4670\n" + 
				"  line 409, col 26 to line 412, col 67 of module Detlefs: 0\n" + 
				"  line 417, col 30 to line 417, col 75 of module Detlefs: 1877\n" + 
				"  line 418, col 30 to line 418, col 50 of module Detlefs: 1877\n" + 
				"  line 419, col 27 to line 419, col 64 of module Detlefs: 1877\n" + 
				"  line 420, col 27 to line 420, col 65 of module Detlefs: 2031\n" + 
				"  line 421, col 37 to line 421, col 55 of module Detlefs: 0\n" + 
				"  line 423, col 27 to line 423, col 64 of module Detlefs: 1877\n" + 
				"  line 424, col 27 to line 424, col 59 of module Detlefs: 1877\n" + 
				"  line 425, col 27 to line 425, col 58 of module Detlefs: 2031\n" + 
				"  line 426, col 27 to line 426, col 38 of module Detlefs: 2031\n" + 
				"  line 427, col 26 to line 430, col 48 of module Detlefs: 0\n" + 
				"  line 433, col 17 to line 433, col 64 of module Detlefs: 3115\n" + 
				"  line 434, col 17 to line 434, col 67 of module Detlefs: 3115\n" + 
				"  line 435, col 17 to line 435, col 67 of module Detlefs: 3115\n" + 
				"  line 436, col 17 to line 436, col 67 of module Detlefs: 3115\n" + 
				"  line 437, col 17 to line 437, col 67 of module Detlefs: 3115\n" + 
				"  line 438, col 17 to line 438, col 73 of module Detlefs: 3115\n" + 
				"  line 439, col 17 to line 439, col 64 of module Detlefs: 3115\n" + 
				"  line 440, col 17 to line 440, col 67 of module Detlefs: 3115\n" + 
				"  line 441, col 27 to line 444, col 41 of module Detlefs: 0\n" + 
				"  line 451, col 16 to line 451, col 55 of module Detlefs: 18876\n" + 
				"  line 452, col 16 to line 452, col 47 of module Detlefs: 18876\n" + 
				"  line 453, col 26 to line 456, col 67 of module Detlefs: 0\n" + 
				"  line 459, col 16 to line 459, col 54 of module Detlefs: 22565\n" + 
				"  line 461, col 27 to line 461, col 65 of module Detlefs: 7619\n" + 
				"  line 462, col 27 to line 462, col 59 of module Detlefs: 7619\n" + 
				"  line 463, col 27 to line 463, col 58 of module Detlefs: 14946\n" + 
				"  line 464, col 27 to line 464, col 38 of module Detlefs: 14946\n" + 
				"  line 465, col 26 to line 468, col 59 of module Detlefs: 0\n" + 
				"  line 471, col 17 to line 471, col 64 of module Detlefs: 5175\n" + 
				"  line 472, col 17 to line 472, col 70 of module Detlefs: 5175\n" + 
				"  line 473, col 17 to line 473, col 70 of module Detlefs: 5175\n" + 
				"  line 474, col 17 to line 474, col 67 of module Detlefs: 5175\n" + 
				"  line 475, col 17 to line 475, col 76 of module Detlefs: 5175\n" + 
				"  line 476, col 17 to line 476, col 79 of module Detlefs: 5175\n" + 
				"  line 477, col 17 to line 477, col 67 of module Detlefs: 5175\n" + 
				"  line 478, col 27 to line 481, col 41 of module Detlefs: 0\n" + 
				"  line 487, col 41 to line 487, col 56 of module Detlefs: 3132\n" + 
				"  line 488, col 41 to line 488, col 57 of module Detlefs: 3132\n" + 
				"  line 489, col 38 to line 489, col 77 of module Detlefs: 3132\n" + 
				"  line 490, col 38 to line 490, col 78 of module Detlefs: 4101\n" + 
				"  line 491, col 48 to line 491, col 70 of module Detlefs: 0\n" + 
				"  line 493, col 38 to line 493, col 69 of module Detlefs: 3132\n" + 
				"  line 494, col 38 to line 494, col 69 of module Detlefs: 4101\n" + 
				"  line 495, col 27 to line 495, col 58 of module Detlefs: 9330\n" + 
				"  line 496, col 37 to line 496, col 67 of module Detlefs: 0\n" + 
				"  line 497, col 26 to line 500, col 48 of module Detlefs: 0\n" + 
				"  line 503, col 16 to line 503, col 62 of module Detlefs: 8102\n" + 
				"  line 504, col 16 to line 504, col 47 of module Detlefs: 8102\n" + 
				"  line 505, col 26 to line 508, col 67 of module Detlefs: 0\n" + 
				"  line 513, col 30 to line 513, col 77 of module Detlefs: 3926\n" + 
				"  line 514, col 30 to line 514, col 50 of module Detlefs: 3926\n" + 
				"  line 515, col 27 to line 515, col 66 of module Detlefs: 3926\n" + 
				"  line 516, col 27 to line 516, col 67 of module Detlefs: 3418\n" + 
				"  line 517, col 37 to line 517, col 55 of module Detlefs: 0\n" + 
				"  line 519, col 27 to line 519, col 58 of module Detlefs: 3926\n" + 
				"  line 520, col 27 to line 520, col 58 of module Detlefs: 3418\n" + 
				"  line 521, col 26 to line 524, col 48 of module Detlefs: 0\n" + 
				"  line 527, col 16 to line 527, col 70 of module Detlefs: 4376\n" + 
				"  line 528, col 16 to line 528, col 47 of module Detlefs: 4376\n" + 
				"  line 529, col 26 to line 532, col 63 of module Detlefs: 0\n" + 
				"  line 535, col 16 to line 536, col 57 of module Detlefs: 3743\n" + 
				"  line 537, col 16 to line 537, col 60 of module Detlefs: 3743\n" + 
				"  line 538, col 16 to line 538, col 48 of module Detlefs: 3743\n" + 
				"  line 539, col 26 to line 542, col 59 of module Detlefs: 0\n" + 
				"  line 545, col 17 to line 545, col 64 of module Detlefs: 2133\n" + 
				"  line 546, col 17 to line 546, col 70 of module Detlefs: 2133\n" + 
				"  line 547, col 17 to line 547, col 70 of module Detlefs: 2133\n" + 
				"  line 548, col 17 to line 548, col 67 of module Detlefs: 2133\n" + 
				"  line 549, col 17 to line 549, col 76 of module Detlefs: 2133\n" + 
				"  line 550, col 17 to line 550, col 79 of module Detlefs: 2133\n" + 
				"  line 551, col 17 to line 551, col 67 of module Detlefs: 2133\n" + 
				"  line 552, col 27 to line 555, col 41 of module Detlefs: 0\n" + 
				"  line 558, col 16 to line 558, col 64 of module Detlefs: 5616\n" + 
				"  line 559, col 16 to line 559, col 48 of module Detlefs: 5616\n" + 
				"  line 560, col 26 to line 563, col 67 of module Detlefs: 0\n" + 
				"  line 566, col 17 to line 566, col 64 of module Detlefs: 3529\n" + 
				"  line 567, col 17 to line 567, col 70 of module Detlefs: 3529\n" + 
				"  line 568, col 17 to line 568, col 70 of module Detlefs: 3529\n" + 
				"  line 569, col 17 to line 569, col 67 of module Detlefs: 3529\n" + 
				"  line 570, col 17 to line 570, col 76 of module Detlefs: 3529\n" + 
				"  line 571, col 17 to line 571, col 79 of module Detlefs: 3529\n" + 
				"  line 572, col 17 to line 572, col 67 of module Detlefs: 3529\n" + 
				"  line 573, col 27 to line 576, col 41 of module Detlefs: 0\n" + 
				"  line 584, col 27 to line 584, col 82 of module Detlefs: 3588\n" + 
				"  line 585, col 27 to line 585, col 60 of module Detlefs: 3588\n" + 
				"  line 586, col 27 to line 586, col 58 of module Detlefs: 7384\n" + 
				"  line 587, col 37 to line 587, col 44 of module Detlefs: 7384\n" + 
				"  line 589, col 27 to line 589, col 64 of module Detlefs: 7384\n" + 
				"  line 590, col 27 to line 590, col 59 of module Detlefs: 7384\n" + 
				"  line 591, col 27 to line 591, col 59 of module Detlefs: 3588\n" + 
				"  line 592, col 27 to line 592, col 38 of module Detlefs: 3588\n" + 
				"  line 593, col 26 to line 596, col 59 of module Detlefs: 0\n" + 
				"  line 599, col 17 to line 599, col 64 of module Detlefs: 3588\n" + 
				"  line 600, col 17 to line 600, col 64 of module Detlefs: 3588\n" + 
				"  line 601, col 17 to line 601, col 73 of module Detlefs: 3588\n" + 
				"  line 602, col 17 to line 602, col 67 of module Detlefs: 3588\n" + 
				"  line 603, col 17 to line 603, col 73 of module Detlefs: 3588\n" + 
				"  line 604, col 17 to line 604, col 79 of module Detlefs: 3588\n" + 
				"  line 605, col 17 to line 605, col 61 of module Detlefs: 3588\n" + 
				"  line 606, col 17 to line 606, col 67 of module Detlefs: 3588\n" + 
				"  line 607, col 27 to line 610, col 41 of module Detlefs: 0\n" + 
				"  line 613, col 17 to line 614, col 59 of module Detlefs: 3669\n" + 
				"  line 615, col 17 to line 615, col 48 of module Detlefs: 3669\n" + 
				"  line 616, col 27 to line 619, col 77 of module Detlefs: 0\n" + 
				"  line 622, col 16 to line 622, col 56 of module Detlefs: 6496\n" + 
				"  line 623, col 16 to line 623, col 47 of module Detlefs: 6496\n" + 
				"  line 624, col 26 to line 627, col 67 of module Detlefs: 0\n" + 
				"  line 630, col 16 to line 630, col 63 of module Detlefs: 8918\n" + 
				"  line 632, col 27 to line 632, col 58 of module Detlefs: 3971\n" + 
				"  line 633, col 27 to line 633, col 58 of module Detlefs: 4947\n" + 
				"  line 634, col 26 to line 637, col 67 of module Detlefs: 0\n" + 
				"  line 640, col 16 to line 640, col 56 of module Detlefs: 3498\n" + 
				"  line 641, col 16 to line 641, col 47 of module Detlefs: 3498\n" + 
				"  line 642, col 26 to line 645, col 67 of module Detlefs: 0\n" + 
				"  line 648, col 16 to line 648, col 57 of module Detlefs: 2743\n" + 
				"  line 649, col 16 to line 649, col 47 of module Detlefs: 2743\n" + 
				"  line 650, col 26 to line 653, col 67 of module Detlefs: 0\n" + 
				"  line 658, col 30 to line 658, col 48 of module Detlefs: 1706\n" + 
				"  line 659, col 30 to line 659, col 49 of module Detlefs: 1706\n" + 
				"  line 660, col 27 to line 660, col 68 of module Detlefs: 1706\n" + 
				"  line 661, col 27 to line 661, col 69 of module Detlefs: 1417\n" + 
				"  line 662, col 37 to line 662, col 59 of module Detlefs: 0\n" + 
				"  line 664, col 27 to line 664, col 64 of module Detlefs: 1706\n" + 
				"  line 665, col 27 to line 665, col 58 of module Detlefs: 1706\n" + 
				"  line 666, col 27 to line 666, col 59 of module Detlefs: 1706\n" + 
				"  line 667, col 27 to line 667, col 58 of module Detlefs: 1417\n" + 
				"  line 668, col 37 to line 668, col 50 of module Detlefs: 0\n" + 
				"  line 669, col 26 to line 672, col 40 of module Detlefs: 0\n" + 
				"  line 675, col 17 to line 675, col 64 of module Detlefs: 1856\n" + 
				"  line 676, col 17 to line 676, col 64 of module Detlefs: 1856\n" + 
				"  line 677, col 17 to line 677, col 73 of module Detlefs: 1856\n" + 
				"  line 678, col 17 to line 678, col 67 of module Detlefs: 1856\n" + 
				"  line 679, col 17 to line 679, col 73 of module Detlefs: 1856\n" + 
				"  line 680, col 17 to line 680, col 79 of module Detlefs: 1856\n" + 
				"  line 681, col 17 to line 681, col 61 of module Detlefs: 1856\n" + 
				"  line 682, col 17 to line 682, col 67 of module Detlefs: 1856\n" + 
				"  line 683, col 27 to line 686, col 41 of module Detlefs: 0\n" + 
				"  line 689, col 16 to line 689, col 62 of module Detlefs: 5083\n" + 
				"  line 690, col 16 to line 690, col 47 of module Detlefs: 5083\n" + 
				"  line 691, col 26 to line 694, col 67 of module Detlefs: 0\n" + 
				"  line 699, col 30 to line 699, col 48 of module Detlefs: 1907\n" + 
				"  line 700, col 30 to line 700, col 76 of module Detlefs: 1907\n" + 
				"  line 701, col 27 to line 701, col 68 of module Detlefs: 1907\n" + 
				"  line 702, col 27 to line 702, col 69 of module Detlefs: 2288\n" + 
				"  line 703, col 37 to line 703, col 54 of module Detlefs: 0\n" + 
				"  line 705, col 27 to line 705, col 64 of module Detlefs: 1907\n" + 
				"  line 706, col 27 to line 706, col 58 of module Detlefs: 1907\n" + 
				"  line 707, col 27 to line 707, col 59 of module Detlefs: 1907\n" + 
				"  line 708, col 27 to line 708, col 58 of module Detlefs: 2288\n" + 
				"  line 709, col 37 to line 709, col 50 of module Detlefs: 0\n" + 
				"  line 710, col 26 to line 713, col 40 of module Detlefs: 0\n" + 
				"  line 716, col 17 to line 716, col 64 of module Detlefs: 3285\n" + 
				"  line 717, col 17 to line 717, col 64 of module Detlefs: 3285\n" + 
				"  line 718, col 17 to line 718, col 73 of module Detlefs: 3285\n" + 
				"  line 719, col 17 to line 719, col 67 of module Detlefs: 3285\n" + 
				"  line 720, col 17 to line 720, col 73 of module Detlefs: 3285\n" + 
				"  line 721, col 17 to line 721, col 79 of module Detlefs: 3285\n" + 
				"  line 722, col 17 to line 722, col 61 of module Detlefs: 3285\n" + 
				"  line 723, col 17 to line 723, col 67 of module Detlefs: 3285\n" + 
				"  line 724, col 27 to line 727, col 41 of module Detlefs: 0\n" + 
				"  line 734, col 16 to line 734, col 50 of module Detlefs: 18005\n" + 
				"  line 735, col 16 to line 735, col 47 of module Detlefs: 18005\n" + 
				"  line 736, col 26 to line 739, col 72 of module Detlefs: 0\n" + 
				"  line 742, col 16 to line 742, col 51 of module Detlefs: 21645\n" + 
				"  line 743, col 16 to line 743, col 47 of module Detlefs: 21645\n" + 
				"  line 744, col 26 to line 747, col 72 of module Detlefs: 0\n" + 
				"  line 751, col 27 to line 751, col 65 of module Detlefs: 9061\n" + 
				"  line 752, col 27 to line 752, col 59 of module Detlefs: 9061\n" + 
				"  line 753, col 27 to line 753, col 58 of module Detlefs: 15463\n" + 
				"  line 754, col 27 to line 754, col 38 of module Detlefs: 15463\n" + 
				"  line 755, col 26 to line 758, col 67 of module Detlefs: 0\n" + 
				"  line 761, col 17 to line 761, col 64 of module Detlefs: 4888\n" + 
				"  line 762, col 17 to line 762, col 64 of module Detlefs: 4888\n" + 
				"  line 763, col 17 to line 763, col 64 of module Detlefs: 4888\n" + 
				"  line 764, col 17 to line 764, col 67 of module Detlefs: 4888\n" + 
				"  line 765, col 17 to line 765, col 70 of module Detlefs: 4888\n" + 
				"  line 766, col 17 to line 766, col 76 of module Detlefs: 4888\n" + 
				"  line 767, col 17 to line 767, col 67 of module Detlefs: 4888\n" + 
				"  line 768, col 27 to line 771, col 50 of module Detlefs: 0\n" + 
				"  line 777, col 41 to line 777, col 56 of module Detlefs: 2809\n" + 
				"  line 778, col 41 to line 778, col 57 of module Detlefs: 2809\n" + 
				"  line 779, col 38 to line 779, col 73 of module Detlefs: 2809\n" + 
				"  line 780, col 38 to line 780, col 74 of module Detlefs: 3448\n" + 
				"  line 781, col 48 to line 781, col 70 of module Detlefs: 0\n" + 
				"  line 783, col 38 to line 783, col 69 of module Detlefs: 2809\n" + 
				"  line 784, col 38 to line 784, col 69 of module Detlefs: 3448\n" + 
				"  line 785, col 27 to line 785, col 58 of module Detlefs: 7680\n" + 
				"  line 786, col 37 to line 786, col 65 of module Detlefs: 0\n" + 
				"  line 787, col 26 to line 790, col 48 of module Detlefs: 0\n" + 
				"  line 793, col 16 to line 793, col 60 of module Detlefs: 6534\n" + 
				"  line 794, col 16 to line 794, col 47 of module Detlefs: 6534\n" + 
				"  line 795, col 26 to line 798, col 71 of module Detlefs: 0\n" + 
				"  line 803, col 30 to line 803, col 49 of module Detlefs: 3265\n" + 
				"  line 804, col 30 to line 804, col 73 of module Detlefs: 3265\n" + 
				"  line 805, col 27 to line 805, col 62 of module Detlefs: 3265\n" + 
				"  line 806, col 27 to line 806, col 63 of module Detlefs: 2621\n" + 
				"  line 807, col 37 to line 807, col 54 of module Detlefs: 0\n" + 
				"  line 809, col 27 to line 809, col 58 of module Detlefs: 3265\n" + 
				"  line 810, col 27 to line 810, col 58 of module Detlefs: 2621\n" + 
				"  line 811, col 26 to line 814, col 53 of module Detlefs: 0\n" + 
				"  line 817, col 16 to line 817, col 66 of module Detlefs: 3619\n" + 
				"  line 818, col 16 to line 818, col 47 of module Detlefs: 3619\n" + 
				"  line 819, col 26 to line 822, col 68 of module Detlefs: 0\n" + 
				"  line 825, col 16 to line 826, col 55 of module Detlefs: 3092\n" + 
				"  line 827, col 16 to line 827, col 59 of module Detlefs: 3092\n" + 
				"  line 828, col 16 to line 828, col 49 of module Detlefs: 3092\n" + 
				"  line 829, col 26 to line 832, col 59 of module Detlefs: 0\n" + 
				"  line 835, col 18 to line 835, col 65 of module Detlefs: 1830\n" + 
				"  line 836, col 18 to line 836, col 65 of module Detlefs: 1830\n" + 
				"  line 837, col 18 to line 837, col 65 of module Detlefs: 1830\n" + 
				"  line 838, col 18 to line 838, col 68 of module Detlefs: 1830\n" + 
				"  line 839, col 18 to line 839, col 71 of module Detlefs: 1830\n" + 
				"  line 840, col 18 to line 840, col 77 of module Detlefs: 1830\n" + 
				"  line 841, col 18 to line 841, col 68 of module Detlefs: 1830\n" + 
				"  line 842, col 28 to line 845, col 51 of module Detlefs: 0\n" + 
				"  line 848, col 16 to line 848, col 62 of module Detlefs: 5041\n" + 
				"  line 849, col 16 to line 849, col 48 of module Detlefs: 5041\n" + 
				"  line 850, col 26 to line 853, col 67 of module Detlefs: 0\n" + 
				"  line 856, col 17 to line 856, col 64 of module Detlefs: 3226\n" + 
				"  line 857, col 17 to line 857, col 64 of module Detlefs: 3226\n" + 
				"  line 858, col 17 to line 858, col 64 of module Detlefs: 3226\n" + 
				"  line 859, col 17 to line 859, col 67 of module Detlefs: 3226\n" + 
				"  line 860, col 17 to line 860, col 70 of module Detlefs: 3226\n" + 
				"  line 861, col 17 to line 861, col 76 of module Detlefs: 3226\n" + 
				"  line 862, col 17 to line 862, col 67 of module Detlefs: 3226\n" + 
				"  line 863, col 27 to line 866, col 50 of module Detlefs: 0\n" + 
				"  line 874, col 24 to line 874, col 66 of module Detlefs: 29212\n" + 
				"  line 875, col 22 to line 875, col 97 of module Detlefs: 29212\n" + 
				"  line 876, col 31 to line 884, col 79 of module Detlefs: 14606\n" + 
				"  line 885, col 31 to line 885, col 72 of module Detlefs: 14606\n" + 
				"  line 886, col 28 to line 886, col 59 of module Detlefs: 14606\n" + 
				"  line 887, col 28 to line 887, col 66 of module Detlefs: 14606\n" + 
				"  line 888, col 28 to line 888, col 62 of module Detlefs: 14606\n" + 
				"  line 889, col 28 to line 889, col 66 of module Detlefs: 14606\n" + 
				"  line 890, col 28 to line 890, col 70 of module Detlefs: 14606\n" + 
				"  line 891, col 28 to line 891, col 59 of module Detlefs: 14606\n" + 
				"  line 892, col 38 to line 892, col 70 of module Detlefs: 0\n" + 
				"  line 893, col 31 to line 901, col 79 of module Detlefs: 14606\n" + 
				"  line 902, col 31 to line 902, col 74 of module Detlefs: 14606\n" + 
				"  line 903, col 28 to line 903, col 61 of module Detlefs: 14606\n" + 
				"  line 904, col 28 to line 904, col 62 of module Detlefs: 14606\n" + 
				"  line 905, col 28 to line 905, col 62 of module Detlefs: 14606\n" + 
				"  line 906, col 28 to line 906, col 62 of module Detlefs: 14606\n" + 
				"  line 907, col 28 to line 907, col 66 of module Detlefs: 14606\n" + 
				"  line 908, col 28 to line 908, col 59 of module Detlefs: 14606\n" + 
				"  line 909, col 38 to line 909, col 74 of module Detlefs: 0\n" + 
				"  line 910, col 32 to line 910, col 94 of module Detlefs: 0\n" + 
				"  line 911, col 28 to line 918, col 76 of module Detlefs: 14606\n" + 
				"  line 919, col 28 to line 919, col 60 of module Detlefs: 14606\n" + 
				"  line 920, col 28 to line 920, col 60 of module Detlefs: 14606\n" + 
				"  line 921, col 28 to line 921, col 62 of module Detlefs: 14606\n" + 
				"  line 922, col 28 to line 922, col 64 of module Detlefs: 14606\n" + 
				"  line 923, col 28 to line 923, col 67 of module Detlefs: 14606\n" + 
				"  line 924, col 28 to line 924, col 59 of module Detlefs: 14606\n" + 
				"  line 925, col 38 to line 925, col 73 of module Detlefs: 0\n" + 
				"  line 926, col 28 to line 933, col 76 of module Detlefs: 14606\n" + 
				"  line 934, col 28 to line 934, col 64 of module Detlefs: 14606\n" + 
				"  line 935, col 28 to line 935, col 64 of module Detlefs: 14606\n" + 
				"  line 936, col 28 to line 936, col 62 of module Detlefs: 14606\n" + 
				"  line 937, col 28 to line 937, col 68 of module Detlefs: 14606\n" + 
				"  line 938, col 28 to line 938, col 69 of module Detlefs: 14606\n" + 
				"  line 939, col 28 to line 939, col 59 of module Detlefs: 14606\n" + 
				"  line 940, col 38 to line 940, col 66 of module Detlefs: 0\n" + 
				"  line 941, col 32 to line 941, col 118 of module Detlefs: 0\n" + 
				"  line 942, col 26 to line 942, col 69 of module Detlefs: 0\n" + 
				"  line 946, col 27 to line 946, col 100 of module Detlefs: 3103\n" + 
				"  line 948, col 37 to line 948, col 42 of module Detlefs: 4276\n" + 
				"  line 949, col 16 to line 949, col 47 of module Detlefs: 7379\n" + 
				"  line 950, col 26 to line 953, col 59 of module Detlefs: 0\n" + 
				"  line 959, col 27 to line 959, col 90 of module Detlefs: 5518\n" + 
				"  line 961, col 37 to line 961, col 42 of module Detlefs: 2506\n" + 
				"  line 962, col 16 to line 962, col 47 of module Detlefs: 8024\n" + 
				"  line 963, col 26 to line 966, col 59 of module Detlefs: 0");
	}
}
