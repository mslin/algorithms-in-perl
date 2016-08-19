#!/usr/bin/perl
#
# count vertex covers and minimal vertex covers in an interval graph
#
# by Min-Sheng Lin
#
use Graph;
use Set::Scalar;	
$|=1;

#globals
$n=12; # problem size: the number of vertices in the interval graph
@v_tag=();
@ab_tag=();
@a=@b=();

@x=@y=();
@vc=@mvc=();

while ( $test++ < 20 ){ # test 20 random instances
	&new_g(); # create a random interval graph
	print "\n== test$test: interval representation: @v_tag ==\n";
	
	print "our proposed algorithm	 :";
	&Compute_x;
	($vc1)=&Count_vc();		
	&Compute_y;
	($mvc1)=&Count_mvc();
	print "#vc=$vc1	 #mvc=$mvc1\n";
		
	print "the brute-force algorithm:";	
	($vc2,$mvc2)=&brute_force(); 
	print "#vc=$vc2	 #mvc=$mvc2\n";
	
	if ( $vc1 != $vc2 || $mvc1 != $mvc2){
		 print "An error occured. Stop!\n";
		 exit;
	}
} # for

print "\n Tests completed successfully.\n";


# compute x set
sub Compute_x {
	@x=();
	$x[0]=0; 
	$h=0;
	for ($s=1; $s <= 2*$n ; $s++){
		$k=$v_tag[$s];
		$ab=$ab_tag[$s];
		if ($ab eq "a"){ # left boundary
			$x[$k]=$h;
		}else{ # right boundary
			$h=$k;
		}
	}
}

# compute the number of vertex covers
sub Count_vc {
	$vc[0]=1;
	for ($k=1; $k <= $n ; $k++){
		$vc[$k]=$vc[$k-1]+$vc[$x[$k]];
	}
	return($vc[$n]);
}

# compute y set
sub Compute_y {
	@y=();
	$y[0]=-1;
	for ($k=1 ; $k<=$n ; $k++){
		if ($y[$k-1] > $x[$k] ){
			$y[$k]=$y[$k-1];
		}else{
			$y[$k]=$x[$k];
		}	
	}
}

#compute the number of minimal vertex covers
sub Count_mvc {
	@mvc=();
	$mvc[0]=1;
	for ($k=1 ; $k<=$n ; $k++){
		$mvc[$k]=$mvc[$k-1]+$mvc[$x[$k]];
		for ($i=$y[$k-1]+1; $i<=$y[$k]; $i++){
			$mvc[$k]=$mvc[$k]-$mvc[$x[$i]];
		}
	}
	return ($mvc[$n]);	
}

# brute force algorithm
sub brute_force {
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);
	%edge=();
	%adj=();
	for ($v=1; $v <= $n-1 ; $v++){
		for ($u=$v+1 ; $u <= $n ; $u++){
			if (!($b[$v] < $a[$u] || $b[$u] < $a[$v])){
				$g->add_edges([$v,$u]);
			}	
		}
	}	
	
	$max=2**$g->vertices-1;
	
	@v_set=();
	@v_set = map { Set::Scalar->new() } 0..$max;
	$vc=0;
	@min_vc_tag=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );		
		@bit =reverse(split(//,$bits));		 	
		%cover=();
		foreach $v ($g->vertices){
			if ($bit[$v-1] == 1){ # select vertex v
				$v_set[$num]->insert($v);						
				foreach $e ($g->edges_at($v)){
					$edge=$$e[0].'-'.$$e[1];
					$cover{$edge}=1;	# v covers edge e
				}					
			}
		} #foreach v
		@cover_edge=keys %cover;

		if ( scalar(keys %cover) == scalar($g->edges) ){ # $v_set[$num] is a vertex cover
			$vc++; 
			# check if $v_set[$num] is a minimal vertex cover
			$min_vc_tag[$num]=1;									 
			foreach $i (0..$num-1){
				if ($min_vc_tag[$i]==1){					
					if ( $v_set[$num]->is_proper_subset($v_set[$i]) ){
						$min_vc_tag[$i]=0; # $v_set[$i] is not a minimal vertex cover						
					}elsif ( $v_set[$num]->is_proper_superset($v_set[$i]) ){
						$min_vc_tag[$num]=0; # $v_set[$num] is not a minimal vertex cover						
						break;
					}
				}
			}
		}
	}
	$mvc=0;
	for ($i=0; $i <= $max ; $i++){
		if ($min_vc_tag[$i]==1){
			$mvc++;
		}
	}
	return($vc, $mvc);
}

# create a random interval graph
sub new_g{
	@v_tag=();
	@ab_tag=();
	@a=@b=();
	
	%p=();
	for ($v=1; $v <=$n ; $v++){
		$p{"$v#a"}=rand(1);
		$p{"$v#b"}=rand(1);
		if ($p{"$v#a"} > $p{"$v#b"}){ #swap
			$tmp=$p{"$v#b"};
			$p{"$v#b"}=$p{"$v#a"};
			$p{"$v#a"}=$tmp;
		}
	}

	# assume vertices from 1 to n are labeled according to their ascending right endpoints (b)
	@key = sort {$p{$b}<=>$p{$a}} keys(%p); #sort by p values from right to left
	
	@v=();
	$pi=2*$n;# scan endpoints from right to left (from 2n to 1)
	$v=$n; # label vertex from right to left in descending order ( from n to 1)
	foreach $k (@key){	# re-arrange the positions of endpoints ai and bi for all vi		
		($vx, $ab)=split("#",$k); 	
		$ab_tag[$pi]=$ab; 				
		if ($ab eq "b"){ #right endpoint
			$v_tag[$pi]=$v;# label vertex v on endpoint pi
			$b[$v]=$pi;		
			$v[$vx]=$v;	# mark vx==>v
			$v--;
		}else{ # left endpoint
			$v_tag[$pi]=$v[$vx];
			$a[$v[$vx]]=$pi;
		}	
		$pi--;	
	}	
}
