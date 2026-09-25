"""Independent small-case checks for explore.py."""

import unittest

from bitset_probe import linear_budget, make_masks, probe_one
from explore import path_length, proved_bound, scan, successors, thue_morse


def brute_length(start: int) -> int:
    """Enumerate path tuples, keeping distinct histories rather than endpoints."""
    paths = [(start,)]
    for depth in range(proved_bound(start) + 1):
        wanted = thue_morse(depth)
        extended = []
        for path in paths:
            u = path[-1]
            for w in (u + 1, u + 2):
                if w < 2:
                    continue
                incoming_label = thue_morse(w) if w == u + 1 else 1 - thue_morse(w)
                if incoming_label == wanted:
                    extended.append(path + (w,))
        if not extended:
            return depth
        paths = extended
    raise AssertionError("the mathematical bound was exceeded")


class PopulationTests(unittest.TestCase):
    def test_thue_morse_recursion(self):
        for n in range(128):
            self.assertEqual(thue_morse(2 * n), thue_morse(n))
            self.assertEqual(thue_morse(2 * n + 1), 1 - thue_morse(n))

    def test_missing_root_edge(self):
        self.assertEqual(successors(0, thue_morse(1)), ())
        self.assertEqual(successors(0, 1 - thue_morse(2)), (2,))

    def test_exact_search_against_path_enumeration(self):
        for start in range(16):
            with self.subTest(start=start):
                self.assertEqual(path_length(start), brute_length(start))

    def test_known_first_values(self):
        expected = [1, 0, 5, 0, 1, 13, 7, 0, 1, 3, 0, 29, 1, 0, 15, 0]
        self.assertEqual(scan(16)["first_16_lengths"], expected)

    def test_statistics_and_stopping_bound(self):
        for start in range(32):
            result = path_length(start, statistics=True)
            self.assertLessEqual(result["length"], proved_bound(start))
            self.assertGreaterEqual(result["maximum_frontier_width"], 1)
            self.assertGreaterEqual(result["visited_depth_endpoint_pairs"], result["length"] + 1)

    def test_bitset_probe_against_exact_frontiers(self):
        largest_start = 255
        masks = make_masks(largest_start + 2 * (linear_budget(largest_start) + 1))
        for start in range(1, largest_start + 1):
            with self.subTest(start=start):
                length_or_bound, exceeded = probe_one(start, masks)
                self.assertFalse(exceeded)
                self.assertEqual(length_or_bound, path_length(start))


if __name__ == "__main__":
    unittest.main()
