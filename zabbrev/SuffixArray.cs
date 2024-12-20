'  VB program for building suffix array of a given text (naive approach)
' Complexity: O(n Log(n) Log(n))
' Modified from: https://www.geeksforgeeks.org/suffix-array-set-2-a-nlognlogn-algorithm/

Imports System
Imports System.Collections.Generic
Imports System.Collections
Imports System.Linq
Imports System.Formats

' Structure to store information of a suffix
Class Suffix
    Public index As Integer
    Public rank As Integer() = New Integer(1) {}

    Public Sub New(ByVal i As Integer, ByVal rank0 As Integer, ByVal rank1 As Integer)
        index = i
        rank(0) = rank0
        rank(1) = rank1
    End Sub
End Class

Class SuffixArrayCompare
    Implements IComparer

    Public Function Compare(ByVal x As Object, ByVal y As Object) As Integer Implements IComparer.Compare
        Dim a As Suffix = CType(x, Suffix)
        Dim b As Suffix = CType(y, Suffix)

        If a.rank(0) <> b.rank(0) Then
            Return a.rank(0) - b.rank(0)
        End If

        Return a.rank(1) - b.rank(1)
    End Function
End Class

Class SuffixArray

    ' This Is the main function that takes a string 'txt' as an
    ' argument, builds And return the suffix array for the given string
    Public Shared Function BuildSuffixArray(text As String) As Integer()
        Dim n As Integer = text.Length

        ' A structure to store suffixes and their indexes
        Dim suffixes As Suffix() = New Suffix(n - 1) {}

        ' Store suffixes And their indexes in an array of structures.
        ' The structure is needed to sort the suffixes alphabetically
        ' And maintain their old indexes while sorting
        For i As Integer = 0 To n - 1
            Dim rank0 As Integer = CInt(Asc(text(i))) - CInt(Asc("a"c))
            Dim rank1 As Integer = If(((i + 1) < n), CInt(Asc(text(i + 1))) - CInt(Asc("a"c)), -1)
            suffixes(i) = New Suffix(i, rank0, rank1)
        Next

        ' Sort the suffixes using the comparison function
        ' defined above.
        Dim cmp As IComparer = New SuffixArrayCompare()
        Array.Sort(suffixes, cmp)

        ' At this point, all suffixes are sorted according to first
        ' 2 characters.  Let us sort suffixes according to first 4
        ' characters, then first 8 And so on
        Dim ind As Integer() = New Integer(n - 1) {}
        ' This array is needed to get the index in suffixes[]
        ' from original index.  This mapping is needed to get
        ' next suffix.

        Dim k As Integer = 4
        While k < 2 * n
            ' Assigning rank and index values to first suffix
            Dim rank As Integer = 0
            Dim prev_rank As Integer = suffixes(0).rank(0)
            suffixes(0).rank(0) = rank
            ind(suffixes(0).index) = 0

            ' Assigning rank to suffixes
            For i As Integer = 1 To n - 1
                ' If first rank and next ranks are same as that of previous
                ' suffix in array, assign the same New rank to this suffix
                If suffixes(i).rank(0) = prev_rank AndAlso suffixes(i).rank(1) = suffixes(i - 1).rank(1) Then
                    prev_rank = suffixes(i).rank(0)
                    suffixes(i).rank(0) = rank
                Else ' Otherwise increment rank and assign
                    prev_rank = suffixes(i).rank(0)
                    suffixes(i).rank(0) = System.Threading.Interlocked.Increment(rank)
                End If

                ind(suffixes(i).index) = i
            Next

            ' Assign next rank to every suffix
            For i As Integer = 0 To n - 1
                Dim nextindex As Integer = suffixes(i).index + k \ 2
                suffixes(i).rank(1) = If((nextindex < n), suffixes(ind(nextindex)).rank(0), -1)
            Next

            ' Sort the suffixes according to first k characters
            Array.Sort(suffixes, cmp)

            k *= 2
        End While

        'Store indexes of all sorted suffixes in the suffix array
        Dim suffixArr As Integer() = New Integer(n - 1) {}

        For i As Integer = 0 To n - 1
            suffixArr(i) = suffixes(i).index
        Next

        Return suffixArr
    End Function


    ' Kasai's algorithm, which can compute this array in  O(n)  time.
    ' Modified from: https://www.geeksforgeeks.org/kasais-algorithm-for-construction-of-lcp-array-from-suffix-array/?ref=ml_lbp
    '                https://stackoverflow.com/questions/57748988/kasai-algorithm-for-constructing-lcp-array-practical-example
    ' The constructered array specifies the number common characters in the prefix between suffix array
    ' position n and position n-1, position 0 in the array is undefined and set to 0 (geeksforgeeks implementation actually
    ' calculates the LCP between n and n+1, here the last position is the undefined one).
    Public Shared Function BuildLCPArray(text As String, suffixArray() As Integer) As Integer()
        Dim n As Integer = text.Length
        Dim lcp(n - 1) As Integer   ' To store LCP array

        ' An auxiliary array to store inverse of suffix array
        ' elements. For example if suffixArray[0] is 5, the
        ' inverseSuffixArray[5] would store 0.
        ' This is used to get next suffix string from suffix array.
        Dim inverseSuffixArray(n - 1) As Integer

        ' Fill values in inverseSuffixArray[]
        For i As Integer = 0 To n - 1
            inverseSuffixArray(suffixArray(i)) = i
        Next

        'Initialize length of previous LCP
        Dim k As Integer = 0

        ' Process all suffixes one by one starting from
        ' first suffix in text[]
        For i As Integer = 0 To n - 1
            If inverseSuffixArray(i) > 0 Then
                ' j contains index of the previous substring to
                ' be considered to compare with the present
                ' substring, i.e., previous string in suffix array
                Dim j As Integer = suffixArray(inverseSuffixArray(i) - 1)

                ' Directly start matching from k'th index as
                ' at-least k-1 characters will match
                While (i + k) < n And (j + k) < n AndAlso text(i + k) = text(j + k)
                    k += 1
                End While

                lcp(inverseSuffixArray(i)) = k ' lcp for the present suffix.

                ' Deleting the starting character from the string.
                If k > 0 Then k -= 1
            Else
                ' If the current suffix Is at 0, then we don't
                ' have previous substring to consider. So lcp is not
                ' defined for this substring, we put zero.
                k = 0
            End If
        Next

        ' return the constructed lcp array
        Return lcp
    End Function

    Public Shared Function BuildGeneralizedSuffixArrayString(texts As List(Of String), Optional seperator As Char = ControlChars.VerticalTab) As String
        Dim allText As String = ""
        For i As Integer = 0 To texts.Count - 1
            allText = String.Concat(allText, texts(i), seperator)
        Next
        Return allText
    End Function

    Public Shared Function BuildGeneralizedSuffixArray(texts As List(Of String), Optional seperator As Char = ControlChars.VerticalTab) As Integer()
        Return BuildSuffixArray(BuildGeneralizedSuffixArrayString(texts, seperator))
    End Function

    ' A fast way to count the number of occurrences of a pattern inside a text when an index of a suffix
    ' that contains the pattern as prefix.
    ' Don't take overlaps into account
    Public Shared Function Count(lcp() As Integer, suffixArrayIndexForOnePattern As Integer, prefixLength As Integer) As Integer
        Return FindLastPositionOfPrefix(lcp, suffixArrayIndexForOnePattern, prefixLength) -
               FindFirstPositionOfPrefix(lcp, suffixArrayIndexForOnePattern, prefixLength) + 1
    End Function

    ' Return the number of occurrences of a pattern inside a text (no accounting for overlaps).
    ' Because we don't where to start we need to find the index of a match first
    Public Shared Function Count(text As String, suffixArray() As Integer, lcp() As Integer, pattern As String) As Integer
        Dim index As Integer = BinarySearch(text, suffixArray, pattern)
        If index = -1 Then Return 0
        Return Count(lcp, index, pattern.Length)
    End Function

    Public Shared Function Contains(pattern As String, text As String, suffixArray() As Integer) As Boolean
        Dim index As Integer = BinarySearch(text, suffixArray, pattern)
        If index > -1 Then Return True
        Return False
    End Function

    Public Shared Function IndexOf(pattern As String, startIndex As Integer, text As String, suffixArray() As Integer, lcp() As Integer) As Integer
        Dim index As Integer = BinarySearch(text, suffixArray, pattern)
        Dim plen As Integer = pattern.Length
        Dim lo As Integer = FindFirstPositionOfPrefix(lcp, index, plen)
        Dim hi As Integer = FindFirstPositionOfPrefix(lcp, index, plen)

        If index = -1 Then Return -1                   ' pattern not found

        ' only one occurrence of pattern
        If lo = hi Then
            If lo >= startIndex Then Return suffixArray(index)
            Return -1
        End If

        ' search for minimum position
        Dim min As Integer = -1
        For i As Integer = lo To hi
            Dim pos As Integer = suffixArray(i)
            If pos >= startIndex And (pos < min Or min = -1) Then min = pos
        Next

        Return min
    End Function

    Public Shared Function CountUniquePatterns(lcp() As Integer) As Long
        Dim n As Long = lcp.Length - Count(lcp, 0, 1)
        Return (n * (n + 1)) \ 2 - lcp.Sum
    End Function

    ' ****************************************************************************************
    ' * Helper functions
    ' ****************************************************************************************

    Public Shared Function BinarySearch(text As String, suffixArray() As Integer, pattern As String) As Integer
        Dim len As Integer = text.Length
        Dim plen As Integer = pattern.Length
        Dim lo As Integer = 0
        Dim hi As Integer = len - plen
        While (lo + 1 < hi)
            Dim mid As Integer = (lo + hi) \ 2

            Dim cmp As Integer = StringCompare(text.Substring(suffixArray(mid)), pattern, plen)

            If cmp = 0 Then
                ' we have a winner
                Return mid
            ElseIf cmp < 0 Then
                lo = mid
            Else
                hi = mid
            End If
        End While

        ' pattern not found
        Return -1
    End Function

    Public Shared Function FindFirstPositionOfPrefix(lcp() As Integer, prefixIndex As Integer, prefixLength As Integer) As Integer
        Dim lo As Integer = prefixIndex
        While lcp(lo) >= prefixLength And lo > 0
            lo -= 1
        End While
        If lo = prefixIndex Then Return prefixIndex
        Return lo + 1
    End Function

    Private Shared Function FindLastPositionOfPrefix(lcp() As Integer, prefixIndex As Integer, prefixLength As Integer) As Integer
        Dim hi As Integer = prefixIndex
        Dim lcpLength As Integer = lcp.Length
        While hi < lcpLength - 1 AndAlso lcp(hi + 1) >= prefixLength
            hi += 1
        End While
        Return hi
    End Function

    ' Compares two strings (in length positions) and return:
    '    0 if the strings are equal
    '   -1 if string1 is before string2
    '    1 if string1 is after string2
    Private Shared Function StringCompare(string1 As String, string2 As String, length As Integer) As Integer
        For i = 0 To length - 1
            If i > string1.Length - 1 Then Return -1
            If string1(i) < string2(i) Then Return -1
            If string1(i) > string2(i) Then Return 1
        Next
        Return 0
    End Function

End Class
