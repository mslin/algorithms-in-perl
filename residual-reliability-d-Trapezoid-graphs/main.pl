#!/usr/bin/perl
#
# Compute the K-terminal residual reliability (KTRR) of a d-trapezoid graph (note: test only the case of d=2)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=10;# the number of vertices (problem size)
$p=0.6;# the reliability of each vertex
$target_p=0.5;# the probability that a vertex is a target vertex

@top=@bottom=(); # the top line and the bottom line of the 2-trapezoid diagram
@Q=();# Q[t][b] store the vertices that cross the scanline s(t,b)
@k_tag=();#store the tag whether v is in K set
%a=%b=%c=%d=();
@torder=(); # store topological order of V
@itorder=();# store invert topological order of V
@SS=();#$SS[$v]: the set of the pair of scanlines (s,t) such that Qv is onctained in Q(s)-Q(t)
%qst=();# qst(st): productions of (1-$p[$v]) for all v in (Q(s)-Q(t))
%qst_k=(); # qst_k(st): productions of all q(w) for all w in Qv(st) and w in K 
%qst_nk=();# qst_nk(st): productions of all q(w) for all w in Qv(st) and w not in K
$g = Graph::Undirected->new(); #for brute-force algorithm

while ( $test++ < 20 ){ # test 20 random instances	
	&new_g(); # create a random 2-trapezoid graph
		
	print "\n== test$test: 2-trapezoid diagram: ==\n";	
	print "@top[1..$#top]\n";	# top line
	print "@bottom[1..$#bottom]\n";	# bottom line
	print "target vertices: ";
	for($v=1; $v<=$n; $v++){ # print target vertices
		print "$v " if ($k_tag[$v]);			
	}
	print "\n";
	
	print "our proposed algorithm:    ";	
	$ktrr1=&Compute_KTRR();
	print "KTRR=$ktrr1\n";
	
	print "the brute-force algorithm: ";		
	$ktrr2=&brute_force();
	print "KTRR=$ktrr2\n";
  
	if (($ktrr1 - $ktrr2 ) > 0.000001 || ($ktrr2 - $ktrr1 ) > 0.000001 ){
		print "An error occured. Stop!\n";
		exit;
	}
}										 
print "\n Tests completed successfully.\n";

sub Compute_KTRR {  
	# Note: qst(st)=productions of all q(w) for all w in Qv(st) when given two endpoints of u, v in K
	# this version will partition qst(st) into two parts: qst(st)=qst_nk(st)*qst_k(st)
	#    1. qst_nk(st)=productions of all q(w) for all w in Qv(st) and w not in K
	#    2. qst_k(st)=productions of all q(w) for all w in Qv(st) and w in K
	# qst_nk(st) is independent of u and v, so it can be precomputed in compute_SS() and always holds the same value
	# qst_k(st) is dependent on u and v, so it will be accmulated during changing of u, v in this procedure
	#
	
	&Compute_Q();#compute Q(s)
	
	&Compute_SS();#compute SS(Qv) and q(s,t)
  
	return( &Compute_PrA());
}	

sub Compute_Q { 
	$top_min=1+0.5;
	$top_max=2*$n-0.5;
	$bottom_min=1+0.5;
	$bottom_max=2*$n-0.5;
	@Q=();
	for ($t=$top_min; $t <= $top_max ; $t++){
	for ($b=$bottom_min; $b <= $bottom_max; $b++){
		$Q[$t][$b]= Set::Scalar->new;
		for($v=1; $v <= $n ; $v++){
			if (!(($b[$v] < $t && $d[$v] < $b) || ($a[$v] > $t && $c[$v] > $b))){
				$Q[$t][$b]->insert($v);
			}
		}
	}}
}


sub Compute_SS {

	@SS=();
	%qst=();
	%qst_nk=();
	
	$tx=$bx=2*$n+0.5;  # dummy scanline
	$Q[$tx][$bx]= Set::Scalar->new;  # empty sets for the dummy scanline
	
	for ($v=1 ; $v <= $n ; $v++){
		$SS[$v]= Set::Scalar->new; # the set of qst(sj-si) in which v is contained
	} 
	
	for ($uu=1; $uu <= $n ; $uu++){
		$u=$torder[$uu-1];
		for ($vv=$uu; $vv <= $n; $vv++){	
			$v=$torder[$vv-1];	
			$top_min=$b[$u]+0.5; $top_max=$a[$v]-0.5;
			$bottom_min=$d[$u]+0.5; $bottom_max=$c[$v]-0.5;
    
			for ($t1=$top_min; $t1 <= $top_max ; $t1++){
			for ($b1=$bottom_min; $b1 <= $bottom_max; $b1++){    

				for ($t2=$top_min; $t2 <= $t1 ; $t2++){
				for ($b2=$bottom_min; $b2 <= $b1; $b2++){
				
					next if ($t1==$t2 && $b1==$b2);	  
					#--- compute SS, qst
					$st="$t2:$b2".'-'."$t1:$b1"; # denote the pair (s,t)
					if (!defined($qst{$st})){						
						$w_st=$Q[$t2][$b2]-$Q[$t1][$b1];
						$qst{$st}=1; # the value of prob(st)                 
						$qst_nk{$st}=1; # the value of prob(st) for w not in k            
						for $w ($w_st->elements){         
							$SS[$w]->insert($st); # w is contained in Q(s)-Q(t)
							if (!$k_tag[$w]){
								$qst{$st} *= (1-$p[$w]);
								$qst_nk{$st} *= (1-$p[$w]);
							} 	
						}
					}
				}}		  
				#-- for dummy scanline
				$st="$t1:$b1-$tx:$bx";  
				$w_st=$Q[$t1][$b1]-$Q[$tx][$bx];
				$qst{$st}=1; # the value of prob(st)     	 
				$qst_nk{$st}=1;
				for $w ($w_st->elements){         
					$SS[$w]->insert($st); # w is contained in Q(s)-Q(t)
					if (!$k_tag[$w]){
						$qst{$st} *= (1-$p[$w]);
						$qst_nk{$st} *= (1-$p[$w]);			   
					} 				
				}  
			}}
		}
	}
}

sub Compute_PrA {
	$PrA=0;  
	for ($uu=1; $uu <= $n ; $uu++){
		$u=$torder[$uu-1];   # u is the uu'th node by the topology order
		next if (!$k_tag[$u]);  # skip if u is a non-target node
		
		&reset_all_qst_k();
		
		for ($vv=$uu; $vv <= $n; $vv++){	
			$v=$torder[$vv-1]; # v is the vv'th node by the topology order
			next if (!$k_tag[$v]); # skip if v is a non-target node
			$PrB=1;  # denote Pr{Bu,v}
			for ($ww=1 ; $ww <= $n ; $ww++){	     
				$w=$torder[$ww-1]; # w is the ww'th node by the topology order
				next if (!$k_tag[$w]); # skip if w is a non-target node
				if ($ww<$uu || $ww > $vv){ # case 1: node w fails
					$PrB*=(1-$p[$w]);		
				}	
				if ($ww==$uu || $ww==$vv){ # case 2: node w works
					$PrB*=$p[$w];		     
				}           
			}			
			$PrRB=&compute_two_terminal_rel($u, $v); # call the algorithm of computing the two-termianl-reliability (from u to v)
			$PrA = $PrA + $PrRB *$PrB;
		
			for $st ($SS[$v]->elements){  # update the qst value of s-t  which contains v 
				$qst_k{$st} *= (1-$p[$v]); 
			}	  
		}
	}
	return($PrA);
}

sub reset_all_qst_k{
	my ($v_st,$t1,$b1,$t2,$b2,$qvs,$st,$v,$u,$uu,$vv,$tx,$bx);
	my ($top_min, $top_max, $bottom_min, $bottom_max);
	%qst_k=();
  
	$tx=$bx=2*$n+0.5;  # dummy scanline

	for ($uu=1; $uu <= $n ; $uu++){
		$u=$torder[$uu-1];
		for ($vv=$uu; $vv <= $n; $vv++){	
			$v=$torder[$vv-1];	
			$top_min=$b[$u]+0.5; $top_max=$a[$v]-0.5;
			$bottom_min=$d[$u]+0.5; $bottom_max=$c[$v]-0.5;
			
			for ($t1=$top_min; $t1 <= $top_max ; $t1++){
			for ($b1=$bottom_min; $b1 <= $bottom_max; $b1++){    
	
				for ($t2=$top_min; $t2 <= $t1 ; $t2++){
				for ($b2=$bottom_min; $b2 <= $b1; $b2++){
					next if ($t1==$t2 && $b1==$b2);	  
	
					$st="$t2:$b2".'-'."$t1:$b1"; # denote s-t	           
					$qst_k{$st}=1;	 # reset
				}}

				#-- for dummy scanline
				$st="$t1:$b1-$tx:$bx";  	      
				$qst_k{$st}=1; # the value of prob(st) for k part
			}}
		}
	}
}


#compute the 2-terminal reliability (from node $x to node $y)
sub compute_two_terminal_rel{  
	my ($x, $y)= @_;  
	my ($t1, $b1, $t2, $b2, $tx, $bx, $two_rel, @prR);
	my ($top_min, $top_max, $bottom_min, $bottom_max);	
	$top_min=$b[$x]+0.5; $top_max=$a[$y]-0.5;
	$bottom_min=$d[$x]+0.5; $bottom_max=$c[$y]-0.5;
      
	for ($t1=$top_min; $t1 <= $top_max ; $t1++){
	for ($b1=$bottom_min; $b1 <= $bottom_max; $b1++){
		$prR[$t1][$b1]=1;        
		for ($t2=$top_min; $t2 <= $t1 ; $t2++){
		for ($b2=$bottom_min; $b2 <= $b1; $b2++){
			next if ($t1==$t2 && $b1==$b2);
			$prR[$t1][$b1] -= $prR[$t2][$b2]*$qst_nk{"$t2:$b2-$t1:$b1"}*$qst_k{"$t2:$b2-$t1:$b1"};
		}}
	}}
	$tx=$bx=2*$n+0.5; # for dummy scanline
	$two_rel=1; 
	for ($t2=$top_min; $t2 <= $top_max ; $t2++){
	for ($b2=$bottom_min; $b2 <= $bottom_max; $b2++){          
		$two_rel -= $prR[$t2][$b2]*$qst_nk{"$t2:$b2-$tx:$bx"}*$qst_k{"$t2:$b2-$tx:$bx"};
	}}
	return($two_rel);  
}

sub brute_force {
	$max=2**$n-1;
	$r=0;
	foreach $i (0..$max){
		$h = $g->copy_graph;		
		$bits = unpack ( "B*", pack("N",$i) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		$pr=1;
		@k_tmp=();
		foreach $v ($h->vertices){  
			$px=$p[$v];
			if ($bit[$v-1] == 1){ # v works
				$pr=$pr*$px;
				if ($k_tag[$v]){
					push(@k_tmp,$v);
				}
			}else{ # v fails
				$pr=$pr*(1-$px);
				$h->delete_vertex($v);
			}
		} #foreach v
		next if ($pr==0);

		next if (scalar(@k_tmp)==0);  # not counting the probability that all k-target vertices fail
		if ($h->same_connected_components(@k_tmp)){
			$r += $pr;
		}    
	}
	return $r;
}

sub new_g{
	@a=@b=@c=@d=();
	@top=@bottom=();
	%p1=%p2=();
	for ($v=1; $v <=$n ; $v++){
		# top line
		$p1{"$v#a"}=rand(1);
		$p1{"$v#b"}=rand(1);
		if ($p1{"$v#a"} > $p1{"$v#b"}){#swap
			$tmp=$p1{"$v#b"};
			$p1{"$v#b"}=$p1{"$v#a"};
			$p1{"$v#a"}=$tmp;
		}
		# bottom line
		$p2{"$v#c"}=rand(1);
		$p2{"$v#d"}=rand(1);
		if ($p2{"$v#c"} > $p2{"$v#d"}){#swap
			$tmp=$p2{"$v#d"};
			$p2{"$v#d"}=$p2{"$v#c"};
			$p2{"$v#c"}=$tmp;
		}	
	}
	
	@key1 = sort {$p1{$a}<=>$p1{$b}} keys(%p1);#sort by p values from left to right
	$pi=0;
	foreach $k (@key1){#re-arrange the positions of endpoints ai and bi for all vi		
		$pi++;
		($v, $ab)=split("#",$k); 	
		$top[$pi]=$v;		
		$ab eq "a" ? $a[$v]=$pi : $b[$v]=$pi;	
	}		
	
	@key2 = sort {$p2{$a}<=>$p2{$b}} keys(%p2); #sort by p values from left to right
	$pi=0;
	foreach $k (@key2){#re-arrange the positions of endpoints ci and di for all vi		
		$pi++;
		($v, $cd)=split("#",$k); 	
		$bottom[$pi]=$v;		
		$cd eq "c" ? $c[$v]=$pi : $d[$v]=$pi;	
	}		

	# set target vertices	and the reliability of each vertex
	for($v=1; $v <= $n ; $v++){
		$p[$v]=$p;
		if (rand(1) < $target_p){
			$k_tag[$v]=1;  # target node
		}else{
			$k_tag[$v]=0; # non-target node
		}
	}
	
	# construct the corresponding d-trape graph g and setup the topological oder <<
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);	
	$gx = Graph->new; # the complement of g
	$gx->add_vertices(1..$n);
	
	for($u=1; $u <= $n; $u++){  
		for($v=1; $v <= $n; $v++){
			next if ($u==$v);
			if( ($b[$u] < $a[$v] && $d[$u] < $c[$v]) || ($b[$v] < $a[$u] && $d[$v] < $c[$u])){# u and v are disconnected
				if ($b[$u] < $a[$v]){# u << v
					$gx->add_edge($u,$v);
				}
			}else{# u and v are connected
				$g->add_edge($u,$v);
			}  
		}   
	}
	@torder = $gx->toposort;  # produce the topological order
	@itorder=();
	for ($i=1 ; $i <= $n ; $i++){
		$u=$torder[$i-1];
		$itorder[$u]=$i-1;
	}
}
