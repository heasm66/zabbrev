//MIT License

//Copyright (c) 2021-2025 Henrik Åsman

//Permission is hereby granted, free of charge, to any person obtaining a copy
//of this software and associated documentation files (the "Software"), to deal
//in the Software without restriction, including without limitation the rights
//to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//copies of the Software, and to permit persons to whom the Software is
//furnished to do so, subject to the following conditions:

//The above copyright notice and this permission notice shall be included in all
//copies or substantial portions of the Software.

//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
//SOFTWARE.

//  VB program for building suffix array of a given text (naive approach)
// Complexity: O(n Log(n) Log(n))
// Modified from: https://www.geeksforgeeks.org/suffix-array-set-2-a-nlognlogn-algorithm/
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;

// Structure to store information of a suffix

namespace zabbrev
{
    internal class Suffix
    {
        public int index;
        public int[] rank = new int[2];

        public Suffix(int i, int rank0, int rank1)
        {
            index = i;
            rank[0] = rank0;
            rank[1] = rank1;
        }
    }

    internal class SuffixArrayCompare : IComparer
    {
        public int Compare(object x, object y)
        {
            Suffix a = (Suffix)x;
            Suffix b = (Suffix)y;

            if (a.rank[0] != b.rank[0])
                return a.rank[0] - b.rank[0];

            return a.rank[1] - b.rank[1];
        }
    }

    internal class SuffixArray
    {

        // This Is the main function that takes a string 'txt' as an
        // argument, builds And return the suffix array for the given string
        public static int[] BuildSuffixArray(string text)
        {
            byte[] byteString = System.Text.Encoding.Latin1.GetBytes(text); // Ensure characters is bytes

            int n = text.Length;

            // A structure to store suffixes and their indexes
            Suffix[] suffixes = new Suffix[n];

            // Store suffixes And their indexes in an array of structures.
            // The structure is needed to sort the suffixes alphabetically
            // And maintain their old indexes while sorting
            for (int i = 0; i < n; i++)
            {
                int rank0 = byteString[i] - (int)'a';
                int rank1 = ((i + 1) < n) ? byteString[i + 1] - (int)'a' : -1;
                suffixes[i] = new Suffix(i, rank0, rank1);
            }

            // Sort the suffixes using the comparison function
            // defined above.
            IComparer cmp = new SuffixArrayCompare();
            Array.Sort(suffixes, cmp);

            // At this point, all suffixes are sorted according to first
            // 2 characters.  Let us sort suffixes according to first 4
            // characters, then first 8 And so on
            int[] ind = new int[n];
            // This array is needed to get the index in suffixes[]
            // from original index.  This mapping is needed to get
            // next suffix.

            int k = 4;
            while (k < 2 * n)
            {
                // Assigning rank and index values to first suffix
                int rank = 0;
                int prev_rank = suffixes[0].rank[0];
                suffixes[0].rank[0] = rank;
                ind[suffixes[0].index] = 0;

                // Assigning rank to suffixes
                for (int i = 1; i < n; i++)
                {
                    // If first rank and next ranks are same as that of previous
                    // suffix in array, assign the same New rank to this suffix
                    if (suffixes[i].rank[0] == prev_rank && suffixes[i].rank[1] == suffixes[i - 1].rank[1])
                    {
                        prev_rank = suffixes[i].rank[0];
                        suffixes[i].rank[0] = rank;
                    }
                    else // Otherwise increment rank and assign
                    {
                        prev_rank = suffixes[i].rank[0];
                        suffixes[i].rank[0] = System.Threading.Interlocked.Increment(ref rank);
                    }

                    ind[suffixes[i].index] = i;
                }

                // Assign next rank to every suffix
                for (int i = 0; i < n; i++)
                {
                    int nextindex = suffixes[i].index + k / 2;
                    suffixes[i].rank[1] = (nextindex < n) ? suffixes[ind[nextindex]].rank[0] : -1;
                }

                // Sort the suffixes according to first k characters
                Array.Sort(suffixes, cmp);

                k *= 2;
            }

            //Store indexes of all sorted suffixes in the suffix array
            int[] suffixArr = new int[n];

            for (int i = 0; i < n; i++)
                suffixArr[i] = suffixes[i].index;

            return suffixArr;
        }


        // Kasai's algorithm, which can compute this array in  O(n)  time.
        // Modified from: https://www.geeksforgeeks.org/kasais-algorithm-for-construction-of-lcp-array-from-suffix-array/?ref=ml_lbp
        //                https://stackoverflow.com/questions/57748988/kasai-algorithm-for-constructing-lcp-array-practical-example
        // The constructered array specifies the number common characters in the prefix between suffix array
        // position n and position n-1, position 0 in the array is undefined and set to 0 (geeksforgeeks implementation actually
        // calculates the LCP between n and n+1, here the last position is the undefined one).
        public static int[] BuildLCPArray(string text, int[] suffixArray)
        {
            int n = text.Length;
            int[] lcp = new int[n]; // To store LCP array

            // An auxiliary array to store inverse of suffix array
            // elements. For example if suffixArray[0] is 5, the
            // inverseSuffixArray[5] would store 0.
            // This is used to get next suffix string from suffix array.
            int[] inverseSuffixArray = new int[n];

            // Fill values in inverseSuffixArray[]
            for (int i = 0; i < n; i++)
                inverseSuffixArray[suffixArray[i]] = i;

            //Initialize length of previous LCP
            int k = 0;

            // Process all suffixes one by one starting from
            // first suffix in text[]
            for (int i = 0; i < n; i++)
            {
                if (inverseSuffixArray[i] > 0)
                {
                    // j contains index of the previous substring to
                    // be considered to compare with the present
                    // substring, i.e., previous string in suffix array
                    int j = suffixArray[inverseSuffixArray[i] - 1];

                    // Directly start matching from k'th index as
                    // at-least k-1 characters will match
                    while ((i + k) < n && (j + k) < n && (text[i + k].ToString())[0] == text[j + k])
                        k += 1;

                    lcp[inverseSuffixArray[i]] = k; // lcp for the present suffix.

                    // Deleting the starting character from the string.
                    if (k > 0) k -= 1;
                }
                else
                {
                    // If the current suffix Is at 0, then we don't
                    // have previous substring to consider. So lcp is not
                    // defined for this substring, we put zero.
                    k = 0;
                }
            }

            // return the constructed lcp array
            return lcp;
        }

        public static string BuildGeneralizedSuffixArrayString(List<string> texts, char seperator = '\v')
        {
            string allText = "";
            for (int i = 0; i < texts.Count; i++)
                allText = string.Concat(allText, texts[i], seperator);
            return allText;
        }

        public static int[] BuildGeneralizedSuffixArray(List<string> texts, char seperator = '\v')
        {
            return BuildSuffixArray(BuildGeneralizedSuffixArrayString(texts, seperator));
        }

        // A fast way to count the number of occurrences of a pattern inside a text when an index of a suffix
        // that contains the pattern as prefix.
        // Don't take overlaps into account
        public static int Count(int[] lcp, int suffixArrayIndexForOnePattern, int prefixLength)
        {
            return FindLastPositionOfPrefix(lcp, suffixArrayIndexForOnePattern, prefixLength) - FindFirstPositionOfPrefix(lcp, suffixArrayIndexForOnePattern, prefixLength) + 1;
        }

        // Return the number of occurrences of a pattern inside a text (no accounting for overlaps).
        // Because we don't where to start we need to find the index of a match first
        public static int Count(string text, int[] suffixArray, int[] lcp, string pattern)
        {
            int index = BinarySearch(text, suffixArray, pattern);
            if (index == -1) return 0;
            return Count(lcp, index, pattern.Length);
        }

        public static bool Contains(string pattern, string text, int[] suffixArray)
        {
            int index = BinarySearch(text, suffixArray, pattern);
            if (index > -1) return true;
            return false;
        }

        public static int IndexOf(string pattern, int startIndex, string text, int[] suffixArray, int[] lcp)
        {
            int index = BinarySearch(text, suffixArray, pattern);
            int plen = pattern.Length;
            int lo = FindFirstPositionOfPrefix(lcp, index, plen);
            int hi = FindFirstPositionOfPrefix(lcp, index, plen);

            if (index == -1) return -1; // pattern not found

            // only one occurrence of pattern
            if (lo == hi)
            {
                if (lo >= startIndex)  return suffixArray[index];
                return -1;
            }

            // search for minimum position
            int min = -1;
            for (int i = lo; i <= hi; i++)
            {
                int pos = suffixArray[i];
                if (pos >= startIndex && (pos < min || min == -1))
                    min = pos;
            }

            return min;
        }

        public static long CountUniquePatterns(int[] lcp)
        {
            long n = lcp.Length - Count(lcp, 0, 1);
            return (n * (n + 1)) / 2 - lcp.Sum();
        }

        // ****************************************************************************************
        // * Helper functions
        // ****************************************************************************************

        public static int BinarySearch(string text, int[] suffixArray, string pattern)
        {
            int len = text.Length;
            int plen = pattern.Length;
            int lo = 0;
            int hi = len - plen;
            while (lo + 1 < hi)
            {
                int mid = (lo + hi) / 2;

                int cmp = StringCompare(text[suffixArray[mid]..], pattern, plen);

                if (cmp == 0) return mid; // we have a winner
                else if (cmp < 0) lo = mid;
                else hi = mid;
            }

            // pattern not found
            return -1;
        }

        public static int FindFirstPositionOfPrefix(int[] lcp, int prefixIndex, int prefixLength)
        {
            int lo = prefixIndex;
            while (lcp[lo] >= prefixLength && lo > 0)
                lo -= 1;
            if (lo == prefixIndex) return prefixIndex;
            return lo + 1;
        }

        private static int FindLastPositionOfPrefix(int[] lcp, int prefixIndex, int prefixLength)
        {
            int hi = prefixIndex;
            int lcpLength = lcp.Length;
            while (hi < lcpLength - 1 && lcp[hi + 1] >= prefixLength)
                hi += 1;
            return hi;
        }

        // Compares two strings (in length positions) and return:
        //    0 if the strings are equal
        //   -1 if string1 is before string2
        //    1 if string1 is after string2
        private static int StringCompare(string string1, string string2, int length)
        {
            for (int i = 0; i < length; i++)
            {
                if (i > string1.Length - 1) return -1;
                if ((string1[i].ToString())[0] < string2[i]) return -1;
                if ((string1[i].ToString())[0] > string2[i]) return 1;
            }
            return 0;
        }

    }

}
