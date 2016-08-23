#!/usr/bin/perl
#
# Count minimal vertexs with minimum/maximum size in an interval graph
#
# by Min-Sheng Lin
#
use Graph;
use Set::Scalar;	
$|=1;

#globals
$n=12; # the problem size
@l=@r=();
@x=@y=();
@v_tag=@lr_tag=();

while ( $test++ < 20 ){ # test 20 random instances
	&new_g();
	print "\n== test$test: interval representation: @v_tag ==\n";
	
	print "our proposed algorithm:    ";
	&Compute_x();
	&Compute_y();	
	$min_mvc1=&Count_n_alpha();
	$max_mvc1=&Fast_Count_n_belta();
	print "#min_mvc=$min_mvc1 #max_mvc=$max_mvc1\n";

	print "the brute-force algorithm: ";
	($min_mvc2,$max_mvc2)=&brute_force();
	print "#min_mvc=$min_mvc2 #max_mvc=$max_mvc2\n";

	if ($min_mvc1 != $min_mvc2 || $max_mvc1 != $max_mvc2){
		 print "An error occured. Stop!\n";
		 exit;
	}
}

print "\n Tests completed successfully.\n";

sub Compute_x {
	@x=();
	$x[0]=0;
	$h=0;
	for ($p=1; $p <= 2*$n ; $p++){
		$k=$v_tag[$p];
		$lr=$lr_tag[$p];
		if ($lr eq 'l'){# left boundary
			$x[$k]=$h;
		}else{# right boundary
			$h=$k;
		}
	}
}

sub Compute_y {
	@y=();
	$y[0]=-1;
	for ($k=1; $k<=$n ; $k++){
		if ($y[$k-1] > $x[$k]){
			$y[$k]=$y[$k-1];
		}else{
			$y[$k]=$x[$k];
		}	
	}	
}

sub Count_n_alpha {
	#first, compute alpha a[k]
	@a=(); # 'a' denotes the 'alpha' in the paper
	$a[0]=0; # initial value
	for ($k=1 ; $k <= $n ; $k++){
		if ($a[$k-1]+1 > $a[$x[$k]]+$k-$x[$k]-1){
			$a[$k]=$a[$x[$k]]+$k-$x[$k]-1;
		}else{
			$a[$k]=$a[$k-1]+1;
		}
	}		
	
	#second, count the #alpha	na[k]
	@na=();	# 'na' deontes the '#alpha' in the paper
	$na[0]=1; # initial value
	for ($k=1 ; $k <= $n; $k++){
		$t=$a[$x[$k]]+$k-$x[$k]-1;
		if ($a[$k-1]+1 < $t){       
			$na[$k]=$na[$k-1];
		}elsif($a[$k-1]+1 > $t){
			$na[$k]=$na[$x[$k]];
		}else{ # $a[$k-1]+1==$t
			$na[$k]=$na[$k-1]+$na[$x[$k]];
		}		
	}
	return ($na[$n]);
}

sub Fast_Count_n_belta {	
	@b=(); # 'b(i)' denotes the 'belta(i)' in the paper
	@nb=();# 'nb(i)' denotes the '#belta(i)' in the paper
	@Q=(); # double end queue
	# Double end Queue Q
	#-------------------<<------ PUSH
	#| 1 | 2 | 3 | ...
	#------------------->>------ POP
	#unshift ----->>------------------
	#                | 1 | 2 | 3 | ...
	#  shift -----<<------------------
	
	$b[0]=0;# initial value
	@Q=(0);# initial value
	$nb[0]=1; # initial value	
	for ($k=1; $k <= $n ; $k++){
		if (&bs($k,$k) > &bs($k,$Q[0])){# step 1, 'bs(i,j)' denotes the 'belta(i,j)' in the paper
			@Q=(); # empty queue
			push @Q,$k; # append k to the rear of Q
			$b[$k]=&bs($k,$k);
			$nb[$k]=$nb[$x[$k]]; # 'nb(x(i))' denotes the '#belta(*,i)' in the paper
		}else{# step 2
			$nb[$k]=$nb[$k-1];
			while ( defined($Q[0]) && $Q[0] < ($y[$k]+1) ){# Q[0] denotes the front of Q, Q(F)
				if (&bs($k-1,$Q[0])==$b[$k-1]){
					$nb[$k]=$nb[$k]-$nb[$x[$Q[0]]];
				}
				shift @Q;# pop front Q
			}
			while (defined($Q[-1]) && (&bs($k,$Q[-1]) < &bs($k,$k)) ){# step 3, Q[-1] dentoes the rear of Q, Q(R)
				pop @Q; # remove the last one from Q
			} 
			push @Q,$k;# append k to the rear of Q   
			$b[$k]=&bs($k,$Q[0]); # step 4
			if ($nb[$k]==0){# step 5: case 1      
				$q=0; # point to the fisrt one of Q 
				while (defined($Q[$q]) && (&bs($k,$Q[$q])==$b[$k]) ){
					$nb[$k] = $nb[$k] + $nb[$x[$Q[$q]]]; 
					$q++; # move to the next one
				}
			} elsif ($b[$k]==&bs($k,$k)){# step 5: case 2
				$nb[$k]=$nb[$k]+$nb[$x[$k]];
			}
		}
	}
	return($nb[$n]); 
}

sub bs{ # 'bs(i,j)' denotes the 'belta(i,j)' in the paper
	local($k,$i)=@_; 
	if ($i==0) { 
		return(0); 
	}else{ 
		return( $b[$x[$i]]+$k-$x[$i]-1 );
	} 
} 

sub brute_force {
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);
	%edge=();
	
	for ($v=1; $v <= $n-1 ; $v++){
		for ($u=$v+1 ; $u <= $n ; $u++){
			if (!($r[$v] < $l[$u] || $r[$u] < $l[$v])){
				$g->add_edges([$v,$u]);
			}	
		}
	}	
	$max=2**$g->vertices-1;
	@vc_set=();
	@vc_set = map { Set::Scalar->new() } 0..$max;
	$number_vc=0;
	@min_vc_tag=();
	%hsize=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		%cover=();
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];
					$cover{$edge}=1;
				}  
				$vc_set[$num]->insert($vs);
			}
		}
		@cover_edge=keys %cover;
		$vc=$vc_set[$num];
		if ( scalar(@cover_edge) == scalar($g->edges) ){
			$number_vc++;       
			$flag=1;
			foreach $i (0..$num-1){
				if ($min_vc_tag[$i]==1){
					$mvi=$vc_set[$i];
					if ( $vc->is_proper_subset($mvi) ){
						$min_vc_tag[$i]=0;
						$flag=1;
					}elsif ( $vc->is_proper_superset($mvi) ){
						$flag=0;
						break;
					}
				}
			}
			if ($flag==1){
				$min_vc_tag[$num]=1;
				$size=$vc->size();
				$hsize{$size}++;
			}
		}
	}
	@size= (sort {$a<=>$b} keys %hsize);
	$msize=$size[0]; $Msize=$size[$#size];
	$minimum_num=$hsize{$msize};
	$maximum_num=$hsize{$Msize};
	return($minimum_num,$maximum_num);
}

# create a random interval graph
sub new_g{
	@v_tag=();
	@lr_tag=();
	@l=@r=();
	
	%p=();
	for ($v=1; $v <=$n ; $v++){
		$p{"$v#l"}=rand(1);
		$p{"$v#r"}=rand(1);
		if ($p{"$v#l"} > $p{"$v#r"}){ #swap
			$tmp=$p{"$v#r"};
			$p{"$v#r"}=$p{"$v#l"};
			$p{"$v#l"}=$tmp;
		}
	}

	# assume vertices from 1 to n are labeled according to their ascending right endpoints (r)
	@key = sort {$p{$b}<=>$p{$a}} keys(%p); #sort by p values from right to left
	
	@v=();
	$pi=2*$n;# scan endpoints from right to left (from 2n to 1)
	$v=$n; # label vertex from right to left in descending order ( from n to 1)
	foreach $k (@key){	# re-arrange the positions of endpoints ai and bi for all vi		
		($vx, $lr)=split("#",$k); 	
		$lr_tag[$pi]=$lr; 				
		if ($lr eq "r"){ #right endpoint
			$v_tag[$pi]=$v;# label vertex v on endpoint pi
			$r[$v]=$pi;		
			$v[$vx]=$v;	# mark vx==>v
			$v--;
		}else{ # left endpoint
			$v_tag[$pi]=$v[$vx];
			$l[$v[$vx]]=$pi;
		}	
		$pi--;	
	}	
}
