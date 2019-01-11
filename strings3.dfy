predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}
predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || pre != str[..|pre|]
}
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}
method isPrefix(pre: string, str: string) returns (res:bool)
ensures !res <==> isNotPrefixPred(pre,str)
ensures  res <==> isPrefixPred(pre,str)
{
  	if(|str| >= |pre|)
	{
		var i := 0;
    	res := true;
		while (i < |pre|)
    	invariant 0 <= i <= |pre|
    	invariant (isPrefixPred(pre[0..i],str) <==> res) || (isNotPrefixPred(pre[0..i],str) <==> !res)
    	decreases |pre| - i
		{
			if(pre[i] != str[i])
			{
        		res := false;
      		}
			i:=i+1;
		}
    	assert i == |pre|;
	}
  	else
  	{
    	res := false;
  	}
  	assert res <==> isPrefixPred(pre,str);
	assert !res <==> isNotPrefixPred(pre,str);
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
ensures  res <==> isSubstringPred(sub, str)
ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	if(|str| >= |sub|)
	{
		var i := 0;
	 	res := false;
		while (i <= |str|-|sub| && !res)
		invariant 0 <= i <= |str|-|sub| + 1
		invariant forall x :: 0 <= x < i ==> isNotPrefixPred(sub, str[x..])
		invariant res ==> isSubstringPred(sub,str)
		decreases |str| - |sub| - i + (if res then 0 else 1)
		{
			res := isPrefix(sub,str[i..]);
			if(res)
			{
				assert isSubstringPred(sub,str) <==> res;
			}
			else
			{
				i := i + 1;
			}
		}
	}
	else
	{
		res := false;
	}
	assert isNotSubstringPred(sub,str) <==> !res;
	assert isSubstringPred(sub,str) <==> res;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	if(|str1| >= k && |str2| >= k )
	{
		var i := 0;
		found := false;
		while((i+k <= |str1|) && !found)
		invariant 0 <= (i+k) <= |str1|+1
		invariant found ==> haveCommonKSubstringPred(k,str1,str2)
		invariant forall x,y :: (0 <= x < i) && !found && y == (x+k) && y <= |str1| ==> isNotSubstringPred(str1[x..y], str2)
		decreases |str1|- (i + k)
		{
			found := isSubstring(str1[i..i+k],str2);
			i := i+1;
		}
		assert found <==> haveCommonKSubstringPred(k,str1,str2);
		assert !found <==> haveNotCommonKSubstringPred(k,str1,str2);
	}
	else
	{
		found := false;
	}
	assert found <==> haveCommonKSubstringPred(k,str1,str2);
	assert !found <==> haveNotCommonKSubstringPred(k,str1,str2);
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	if(|str1|>0)
	{
		var k := |str1|;
		var temp := false;
		while(k > 0 && !temp)
		invariant k >= 0
		invariant temp ==> haveCommonKSubstringPred(k, str1, str2)
		invariant forall x :: k < x <= |str1| ==> !haveCommonKSubstringPred(x, str1, str2)
		decreases k - 0
		{
			temp := haveCommonKSubstring(k,str1,str2);
			if(temp)
			{
				assert haveCommonKSubstringPred(k, str1, str2);
				return k;
			}
			k := k - 1;
		}
		assert isPrefixPred(str1[0..0],str2[0..]);
		assert haveCommonKSubstringPred(k,str1,str2);
		assert k == 0;
		len := k;
	}
	else
	{
		assert isPrefixPred(str1[0..0],str2[0..]);
		len := 0;
	}
}