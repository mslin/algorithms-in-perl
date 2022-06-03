#!/usr/bin/perl
# Count dominating sets in a rooted path-tree bipartite graph
# by Min-Sheng Lin
use Set::Scalar;
use Tree::Simple;
use Graph;
use Graph::Undirected;
#globals
$max_node_size=5; # root size
$max_children=5;
$max_depth=7;
$max_extra=3;
$max_from_parent=3;
$null=Set::Scalar->new();
$g = Graph::Undirected->new(); # the rooted path-tree bipartite graph
@adj=();
%order=();
$ny=$nx=0;
@order=();
@start=();
@post_order=();

#-- main testing --
while ( $test++ < 3000){ # test 3000 random instances			
	$kr=&create_tree(); # create the rooted directed tree of a random rooted path-tree bipartite graph  	
	next if ($nx+$ny > 15);	 # due to the limitation of the brute-force method	
	&construct_graph(); # transfer the rooted path-tree to the corresponding bipartite graph	
	print "== test $test: rooted path-tree bipartite graph: nx=$nx ny=$ny ==\n";
	print "graph: $g\n";
	#print print_tree($kr);
	($DS1)=&brute_force();	
	print "the brute-force algorithm: #DS = $DS1\n";
	($DS2)=&Count_DS($kr);  
	print "   the proposed algorithm: #DS = $DS2\n";	
	($DS3)=&Count_DSx($kr);  
	print "the unpublished algorithm: #DS = $DS3\n";		
	if ($DS2 != $DS1 or $DS3 != $DS1){
		print "An error occured. Stop!\n";
		exit(0);
	}
	$kr->DESTROY();
	print "\n";
} # while test
print "\n Tests completed successfully.\n";

#----- the origial verion in the paper; time complexity: O(X*Y^4) -----
sub Count_DS { 
	my ($kr)=@_;		
	my (@A,@B,@C, $i, $j, $k, $x, $y, $DS);	
	@A=();@B=(); @C=(); # assume that all initial values are zero
	@post_order=();
	&post_order_traversal($kr);
	foreach $node (@post_order){
		$x=$node->getUID;		
		if ($node->isLeaf){	# node x is a leaf node
			if ( ($node->getNodeValue()->elements)[0] > $ny ){ # element 0 is a dummy node 
				$dummy=($node->getNodeValue()->elements)[0];
				$v=($node->getNodeValue()->elements)[1];				
			}else{
				$dummy=($node->getNodeValue()->elements)[1];
				$v=($node->getNodeValue()->elements)[0];
			}				
			#-- compute A, B, C by Lemma 1 --
			$A[$x][$dummy][$v]=1; # {{dummy}}
			$A[$x][$v][$dummy]=0; # {}
			$B[$x][$v]=1; # {{dummy, v}}			
			$B[$x][$dummy]=0; # {}						
			$C[$x]=0; # {}
			next;
		}
		#-- node x is an internal node --
		$Vx=$node->getNodeValue;
		#-- compute A(x,v,u) by Lemma 2	--
		foreach $v ($Vx->elements){
			foreach $u ($Vx->elements){
				if ($u != $v){
					$A[$x][$v][$u]=1;
					foreach $cnode ($node->getAllChildren()){
						$w=$cnode->getUID;	
						$Vw=$cnode->getNodeValue;
						if ($Vw->has($v) and $Vw->has($u)){
							$S = $A[$w][$v][$u];
						}elsif ($Vw->has($v) and !$Vw->has($u)){
							$S = $B[$w][$v];
							foreach $u2 ($Vw->elements){
								$S += $A[$w][$v][$u2] if ($order[$u2] > $order[$u]);
							}							
						}elsif (!$Vw->has($v) and $Vw->has($u)){
							$S=0;
							foreach $v2 ($Vw->elements){
								$S += $A[$w][$v2][$u] if ($order[$v2] < $order[$v]);									
							}														
						}else{	# !$Vw->has($v) and !$Vw->has($u)
							$S = $C[$w];
							foreach $v2 ($Vw->elements){
								if ($order[$v2] < $order[$v]){
									foreach $u2 ($Vw->elements){
										$S += $A[$w][$v2][$u2] if ($order[$u2] > $order[$u]);
									} # foreach u2	
									$S += $B[$w][$v2];
								} # if order								
							} # foreach v2
						} #else						
						$A[$x][$v][$u] *= $S;						
					} # foreach c node					
				}# if u != v
			} # foreach u			
		} # foreach v
		#-- compute B(x,v) by Lemmas 3 and 4 --
		foreach $v ($Vx->elements){
			$B1[$x][$v]=1; # consider the case of containing x
			$B2[$x][$v]=1; # consider the case of not containing x
			foreach $cnode ($node->getAllChildren()){
				$w=$cnode->getUID;	
				$Vw=$cnode->getNodeValue;
				#-- compute B1[$x][$v] --
				if ($Vw->has($v)){
					$S1=$B[$w][$v];
					foreach $u ($Vw->intersection($Vx)->elements){
						$S1 += $A[$w][$v][$u] if ($u != $v);
					}
					$S2=$B[$w][$v];
				}else{
					$S1=$C[$w];
					foreach $v2 ($Vw->elements){
						$S1 += $B[$w][$v2] if ($order[$v2] < $order[$v]);
					} # foreach v2					
					foreach $v2 ($Vw->elements){
						if ($order[$v2] < $order[$v]){
							foreach $u2 ($Vw->intersection($Vx)->elements){
								$S1 += $A[$w][$v2][$u2] if ($u2 != $v2);
							}
						}	
					}					
					$S2=$C[$w];
					foreach $v2 ($Vw->elements){
						$S2 += $B[$w][$v2] if ($order[$v2] < $order[$v]); # && $v2 != 0 ??
					} # foreach v2	
				}							
				$B1[$x][$v] *= $S1;
				$B2[$x][$v] *= $S2;
			} # foreach cnode
			$B[$x][$v]=$B1[$x][$v]+$B2[$x][$v];
		} # foreach v
		#-- compute C(x) by Lemma 5 --
		$C[$x]=1;
		foreach $cnode ($node->getAllChildren()){
			$w=$cnode->getUID;	
			$Vw=$cnode->getNodeValue;
			$S=$C[$w];
			foreach $v2 ($Vw->difference($Vx)->elements){
				$S += $B[$w][$v2];
				foreach $u2 ($Vw->intersection($Vx)->elements){
					$S += $A[$w][$v2][$u2];
				}	
			} # foreach v			
			$C[$x] *= $S;			
		} # foreach cnode		
	} # for each k node 	
	#-- final result --
	$r=$kr->getUID;
	$DS=$C[$r];
	foreach $v ($kr->getNodeValue()->elements){
		$DS += $B[$r][$v];
	}	
	return($DS);
}#--- end of DS ----

#----- the unpublished algorithm (no need of "foreach w in child(x)" loop); time complexity: O(X*Y^2)
sub Count_DSx {
	my ($kr)=@_;		
	my (@A,@B,@C, $w, $j, $k, $x, $y, $DS);	
	@A=();@B=(); @C=(); @AU=();# assume all initial values are zero
	@post_order=();
	&post_order_traversal($kr);
	foreach $node (@post_order){
		$x=$node->getUID;		
		if ($node->isLeaf){			
			if ( ($node->getNodeValue()->elements)[0] > $ny ){ # element 0 is a dummy node 
				$dummy=($node->getNodeValue()->elements)[0];
				$v=($node->getNodeValue()->elements)[1];				
			}else{
				$dummy=($node->getNodeValue()->elements)[1];
				$v=($node->getNodeValue()->elements)[0];
			}				
			$A[$x][$dummy][$v]=1; # {{dummy}}
			$AU[$x][$dummy]=1;
			$A[$x][$v][$dummy]=0; # {}
			$AU[$x][$v]=0;
			$B[$x][$v]=1; # {{dummy, v}}			
			$B[$x][$dummy]=0; # {}						
			$C[$x]=0; # {}
			$N[$dummy]=$N[$v]=$x;  # the NodeId of v and dummy is x
			next;
		}
		#-- node x is an internal node --
		$Vx=$node->getNodeValue;		
		$childCount=$node->getChildCount;
		#-- the new version to compute A(x,v,u) --
		@Sv=@Su=@Sw=@Sb=();				
		$W=Set::Scalar->new();				
		foreach $cnode ($node->getAllChildren()){
			$W = $W + $cnode->getNodeValue;
			$w=$cnode->getUID;
			$Sb[$w]=0; # initial value of Sb
			foreach $u ($W->elements) {
				$Sv[$w][$u]=0;  # initial values of Sv
			}			
		}
		@sortVx=sort {$order[$a] <=> $order[$b]} $W->elements;
		@rsortVx=reverse(@sortVx);
		foreach $v (@sortVx){				
			$vi=$N[$v];
			$AU[$x][$v]=0; # initial value of AU
			$childPos=0;
			$SS=1;
			foreach $cnode ($node->getAllChildren()){
				$w=$cnode->getUID;						
				$Su[$w]=0;	# initial values of Su and Sw
				$Sw[$w]=0;	
				if (($Sw[$w]+$Sb[$w]+$C[$w]) > 0){
					$childPos++;
					$SS *= ($Sw[$w]+$Sb[$w]+$C[$w]);
				}
			}					
			foreach $u (@rsortVx){	
				$ui=$N[$u];				
				next if ($u==$v);
				#-- update A[x][v][v] --
				if ($adj[$x][$v] and $adj[$x][$u]){#$Vx->has($v) && $Vx->has($u)) {
					$A[$x][$v][$u]=1; #!!!!					
					$Swui=$Sw[$ui]+$Sb[$ui] +$C[$ui];
					if ($ui==$vi){	# v and u are in the same node								
						if ($Swui == 0 and $childPos + 1 < $childCount){
							$A[$x][$v][$u] = 0;
						}elsif ($Swui > 0 and $childPos < $childCount){
							$A[$x][$v][$u] = 0;
						}else{	# childPos (or +1) == $childCount							
							$A[$x][$v][$u] = $A[$ui][$v][$u] * $SS;
							$A[$x][$v][$u] /= $Swui if ($Swui > 0);
						}	
					}else{ #ui != vi; v and u not in the same node 
						$Swui=$Sw[$ui]+$Sb[$ui] +$C[$ui];
						$Swvi=$Sw[$vi]+$Sb[$vi] +$C[$vi];
						if ($Swui == 0 && $Swvi == 0 && $childPos + 2 < $childCount){
							$A[$x][$v][$u] = 0;
						}elsif ($Swui > 0 && $Swvi == 0 and $childPos + 1 < $childCount){
							$A[$x][$v][$u] = 0;
						}elsif ($Swui== 0 && $Swvi > 0 and $childPos + 1 < $childCount){
							$A[$x][$v][$u] = 0;
						}elsif ($Swui > 0 && $Swvi > 0 and $childPos  < $childCount){
							$A[$x][$v][$u] = 0;
						}else{	# childPos (or +1, +2) == $childCount
							$A[$x][$v][$u] = ($Su[$vi]+ $B[$vi][$v])* $Sv[$ui][$u] * $SS;
							$A[$x][$v][$u] /= $Swui if ($Swui > 0);
							$A[$x][$v][$u] /= $Swvi if ($Swvi > 0);
						}
					}# else ui != vi		
					$AU[$x][$v] += $A[$x][$v][$u] if ($start[$u]!=$x); # update AU[x][v]
				} #if Vx has u and v							
				$childPos++ if ( ($Sw[$ui]+$Sb[$ui]+$C[$ui]) == 0 && $Sv[$ui][$u] > 0); # check if Sw is positive after updating?	
				
				$SS = $SS / ($Sw[$ui]+$Sb[$ui]+$C[$ui]) if (($Sw[$ui]+$Sb[$ui]+$C[$ui])> 0); # update Sw and SS
				$Sw[$ui] += $Sv[$ui][$u]; # update Sw
				$SS = $SS * ($Sw[$ui]+$Sb[$ui]+$C[$ui]) if (($Sw[$ui]+$Sb[$ui]+$C[$ui])> 0);	
				#-- update Su and Sv --
				if ($vi==$ui){ # v and u are in the same node vi=ui					
					$Su[$vi] += $A[$vi][$v][$u];
					$Sv[$ui][$u] += $A[$ui][$v][$u];
				}									
			} #foreach u
			$Sb[$vi] += $B[$vi][$v]; # update Sb
		}#foreach v
		#-- the new version to compute A(x,v,u)	--
		#-- compute B1(x,v) that contains x --
		@Si=();
		$SS=1;
		$childPos=0;		
		foreach $cnode ($node->getAllChildren()){
			$w=$cnode->getUID;
			$Si[$w]=$C[$w];  # initial value
			if ($Si[$w] > 0){
				$childPos++;
				$SS *= $Si[$w];
			}
		}			
		foreach $v (@sortVx){			
			$w=$N[$v];								
			#-- compute B1 --
			if ($adj[$x][$v]){#$Vx->has($v)
				if ( $Si[$w]==0 && $childPos+1 < $childCount ){
					$B1[$x][$v]=0;
				}elsif( $Si[$w] > 0 && $childPos < $childCount){
					$B1[$x][$v]=0;
				}else{					
					$B1[$x][$v] = ($B[$w][$v] + $AU[$w][$v]) * $SS;
					$B1[$x][$v] /= $Si[$w] if ( $Si[$w] > 0);
				}									
			} # if Vx has v			
			$childPos++ if ($Si[$w]==0 && ($B[$w][$v]+$AU[$w][$v])>0); # the first nonzero in node w
			#-- update SS --
			$SS = $SS / $Si[$w] if ($Si[$w] > 0);
			$Si[$w] += $B[$w][$v] + $AU[$w][$v]; # update the summation of B[w][v]s + AU[w][v] in node w
			$SS = $SS * $Si[$w] if ($Si[$w] > 0);
		} # foreach v	

		#-- compute B2(x,v) that does not contain x --
		@Si=();
		$SS=1;
		$childPos=0;		
		foreach $cnode ($node->getAllChildren()){
			$w=$cnode->getUID;
			$Si[$w]=$C[$w];  # initial value
			if ($Si[$w] > 0){
				$childPos++;
				$SS *= $Si[$w];
			}
		}			
		foreach $v (@sortVx){			
			$w=$N[$v];
			#-- compute B2 --
			if ($adj[$x][$v]){#$Vx->has($v)
				if ( $Si[$w]==0 && $childPos+1 < $childCount ){
					$B2[$x][$v]=0;
				}elsif( $Si[$w] > 0 && $childPos < $childCount){
					$B2[$x][$v]=0;
				}else{					
					$B2[$x][$v] = $B[$w][$v] * $SS;
					$B2[$x][$v] /= $Si[$w] if ( $Si[$w] > 0);
				}					
			} # if Vx has v		
			$childPos++ if ($Si[$w]==0 && $B[$w][$v]>0); # the first nonzero in node w				
			#-- update SS --
			$SS = $SS / $Si[$w] if ($Si[$w] > 0);
			$Si[$w] += $B[$w][$v];	# update the summation of B[w][v]s in node w
			$SS = $SS * $Si[$w] if ($Si[$w] > 0);
		} # foreach v					
		foreach $v ($Vx->elements){
			$N[$v]=$x;
			$B[$x][$v]=$B1[$x][$v]+$B2[$x][$v];
		}
		#-- compute C(x) --
		@Si=();
		foreach $cnode ($node->getAllChildren()){			
			$w=$cnode->getUID;
			$Si[$w]=$C[$w];  # initial value
		}			
		foreach $v ($W->difference($Vx)->elements){
			$w=$N[$v];
			$Si[$w] += $B[$w][$v] + $AU[$w][$v];
		} # foreach v
		$C[$x]=1;
		foreach $cnode ($node->getAllChildren()){
			$w=$cnode->getUID;
			$C[$x] *= $Si[$w];
		}	
		#-- update N[v] --
		foreach $v ($Vx->elements){
			$N[$v]=$x;		
		}
	} # for each x node 
	#-- final result --
	$r=$kr->getUID;
	$DS=$C[$r];
	foreach $v ($kr->getNodeValue()->elements){
		$DS += $B[$r][$v];
	}	
	return($DS);
}#----- end of DSx -----

#----- brute-force algorithm; time complexity: O(2^(|x|+|Y|)) -----
sub brute_force {
	%edge=();  
	$max=2**$g->vertices-1;	
	$nds=0; # for counting dominating sets
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );		
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		$dominating_vertices= Set::Scalar->new;  # for counting dominating sets
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];		
					$dominating_vertices->insert($$a[0],$$a[1]);# for counting dominating sets					
				}  
			}
		}	
		$nds++ if ($dominating_vertices->size == scalar($g->vertices));
	} # foreach num
	return($nds); 
}

#----- create the rooted directed tree of a random rooted path-tree bipartite graph -----
sub create_tree {
	$x=0; # reset the tree node id;
	$ny=$nx=0;  # reset;
	@adj=(); # reset;
	my($i,$j,$x,$y,$n,$s,$child,$fp,$fps,$k,$ki,$ksize,@queue,@knode_member, @kinode_member);
	#-- Step 1: create a random bipartite tree --
	$y=int(rand($max_node_size))+1; # 1 ~ $max_node_size 
	$kr = Tree::Simple->new(Set::Scalar->new(1..$y));
	$kr->setUID(++$x);
	for ($j=1; $j<=$y; $j++){
		$adj[$x][$j]=1;
	}	
	push(@queue,$kr);
	while ($k=shift(@queue)){
		next if ( $k->getDepth() == $max_depth );
		$child=int(rand($max_children+1)); # 0~ $max_children	
		@knode_member=$k->getNodeValue()->elements();
		$ksize=$k->getNodeValue()->size();
		$endflag=0; $i=0;    
		$fps=0;
		while ($i < $child && !$endflag){
			$fp=int(rand($max_from_parent))+1;	  
			$fps += $fp;
			if ($fps > $ksize){
				$endflag=1;
			}else{
				@kinode_member=();		
				for ($j=0,$s=0; $s < $fp; $j=($j+1)%$ksize){     
					next if (!$knode_member[$j]);         
					push(@kinode_member,$knode_member[$j]);
					$knode_member[$j]=0;		  
					$s++;		  
				}		
				$extra=int(rand($max_extra));	  		
				for ($j=0; $j < $extra ; $j++){
					push(@kinode_member,++$y);
				}  
				$ki=Tree::Simple->new(Set::Scalar->new(@kinode_member),$k);
				$ki->setUID(++$x);
				foreach $j (@kinode_member){
					$adj[$x][$j]=1;
				}		
				push(@queue,$ki);
			}#else
			$i++; # next child
		}#while $i < $child
	} # while shift queue 
	$ny=$y;      # the number of y vertices  
	$nx=$x;      # he number of x vertices 
	#-- Step 2: extend the leaf node for each y vertex --
	push(@queue,$kr);	
	while ($node=shift(@queue)){ # level-order traversal
		$yk=$node->getNodeValue;
		$yki = Set::Scalar->new;
		foreach $cnode ($node->getAllChildren()){
			push(@queue,$cnode);
			$yki = $yki + $cnode->getNodeValue;
		}
		$endy=$yk-$yki; #endy is the set of y vertices that end in node $node
		foreach $ey ( $endy->elements){ 
			$leaf=Tree::Simple->new(Set::Scalar->new($ey,++$y),$node); #attach a leaf node containg ey and dummy ++y to node k
			$leaf->setUID(++$x);		
			foreach $j ($ey, $y){
				$adj[$x][$j]=1;	
			}
		}
	}		
	#-- topological sort for each vertex y according to its starting node in the tree --
	$sn=$y; undef @order; undef @start;
	push(@queue,$kr);		
	while ($node=shift(@queue)){ # level-order traversal		
		push(@queue,$node->getAllChildren());				
		foreach $v ($node->getNodeValue()->elements){
			if ( ! exists $order[$v] ){ # visit v for the first time
				$start[$v]=$node->getUID;
				$order[$v]=$sn--;				
			}			
		}		
	}	
	return($kr);
}

sub construct_graph {
	use Graph;
	$g = Graph::Undirected->new();
	for ($a=1; $a<=$nx; $a++){ 
		for ($b=1; $b<=$ny; $b++){      
			$g->add_edges([$ny+$a,$b]) if ($adj[$a][$b]); # $a is shifted ny positions
		}
	}
}

sub post_order_traversal{
	my ($t)=@_;   
	my ($c);   
	return if (!$t); # null node
	foreach $c ($t->getAllChildren()){
		&post_order_traversal($c); 
	}
	push(@post_order,$t); 
}

sub print_tree{
	my($tree)=@_;
	print "root=\n",$tree->getUID,$tree->getNodeValue(),"\n";
	$tree->traverse(sub {
		my ($_tree) = @_;
		print "\t";
		print (("\t" x $_tree->getDepth()),$_tree->getUID, $_tree->getNodeValue(), "\n");
	});
}