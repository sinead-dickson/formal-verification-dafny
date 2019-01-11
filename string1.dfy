
method isPrefix(pre: string, str: string) returns (res:bool)
{
	if(|str|>=|pre|>0)
	{
		var i:=0;
		while(i<|pre|)
		{
			if(pre[i] != str[i]){return false;}
			i:=i+1;
		}
		return true;
	}
	return false;
}

method isSubstring(sub: string, str: string) returns (res:bool)
{
	if(|str|>=|sub|>0)
	{
		var i:=0;
		var temp:=false;
		while(i<=(|str|-|sub|))
		{
			temp:=isPrefix(sub,str[i..]);
			if(temp==true) {res := true;}
			i:=i+1;
		}
	}
	res:= false;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
{
	if(k==0) {return true;}
	if(|str1|>0 && |str2|>0)
	{
		var i:=0;
		var temp:=false;
		while((i+k)<=(|str1|))
		{
			temp := isSubstring(str1[i..(i+k)],str2);
			if(temp == true){return true;}
			i:=i+1;
		}
		return false;
	}
	return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
{
	if(|str1|>0 && |str2|>0)
	{
		var k:=0;
		var temp:=false;
		var max_k:=0;
		while(k<=|str1| && k<=|str2|)
		{
			temp:= haveCommonKSubstring(k,str1,str2);
			if(temp==true)
			{
				max_k := k;
				k:=k+1;
			}
			else
			{
				return max_k;
			}
		}
		return max_k;
	}
	return 0;
}
