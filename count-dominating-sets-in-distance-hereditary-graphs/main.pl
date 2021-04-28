#!/usr/bin/perl
#
# Count dominating sets, connected dominating sets, and total dominating sets in a distance-hereditary graph
#
# Time complexity: O(n)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph::Undirected;
use Tree::Binary;

#globals
$n=12; 	# problem size
$p1=1; $p2=1; $p3=1;  # the ratio of "pendant : false twins : true twins"

@op=();
@twin=();
$g=$dtree='';
@post_order=();

$limit=14; # the limitation for brute-force method
while ( $test++ < 3000 ){ # test 3000 random instances	  
	
	&new_g(); # create a random distance-hereditary graph	
	$dtree=&construct_decomposition_tree();
	#&print_decomposition_tree($dtree);
	print "\n== test $test: distance hereditary graph: ==\n";	
	print "g : $g\n";

	print "\nour proposed algorithm	 : ";		

	$DS1=&DS();
	$CDS1=&CDS();
	$TDS1=&TDS();	
	print "DS=$DS1, CDS=$CDS1, TDS=$TDS1\n";
	
	print "the brute-force algorithm: ";
	($DS2,$CDS2,$TDS2)=&brute_force();
	print "DS=$DS2, CDS=$CDS2, TDS=$TDS2\n";

	if( $DS1!=$DS2 || $CDS1!=$CDS2 || $TDS1 != $TDS2){
		print "An error occured. Stop!\n";
		exit;
	}
	
}
print "\n Tests completed successfully.\n";


# count total dominating sets (TDSs) in a distance-hereditary graph
# the same as couting DS except the initial values of leaf nodes
sub TDS {
	my (@a,@b,@c,@d, $i, $j, $k, $op);
	@post_order=(); # reset
	&post_order_traversal($dtree);
	foreach $node (@post_order){
		$k=$node->getUID;
		if ($node->isLeaf){
			$a[$k]=0; # note: $a[$k]=1 for DS
			$b[$k]=0;
			$c[$k]=1; # note: $a[$k]=0 for DS
			$d[$k]=1;			
		} else {
			$i=$node->getLeft->getUID;
			$j=$node->getRight->getUID;
			$op=$node->getNodeValue;	
			if($op eq 'F'){# op = false twin
				$a[$k]=$a[$i]*($a[$j]+$b[$j]) + $b[$i]*$a[$j];
				$b[$k]=$b[$i]*$b[$j];
				$c[$k]=$a[$i]*($c[$j]+$d[$j]) + $b[$i]*$c[$j] + $c[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $d[$i]*($a[$j]+$c[$j]); 
				$d[$k]=$b[$i]*$d[$j] + $d[$i]*($b[$j]+$d[$j]); 
			}elsif($op eq 'T'){# op = true twin
				$a[$k]=$a[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $b[$i]*$a[$j] + $c[$i]*($a[$j]+$c[$j]) + $d[$i]*$a[$j]; 
				$b[$k]=$b[$i]*$b[$j];
				$c[$k]=$b[$i]*$c[$j] + $c[$i]*($b[$j]+$d[$j]) + $d[$i]*$c[$j]; 
				$d[$k]=$b[$i]*$d[$j] + $d[$i]*($b[$j]+$d[$j]); 
			}else{# op = pendant      
				$a[$k]=$a[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $c[$i]*($a[$j]+$c[$j]);				
				$b[$k]=$b[$i]*($a[$j]+$b[$j]) + $d[$i]*$a[$j]; 
				$c[$k]=$c[$i]*($b[$j]+$d[$j]);				
				$d[$k]=$d[$i]*$b[$j];						
			}	# else	op = pendant
		}	#else not leaf
	} # foreach node		
	return($a[$k]+$b[$k]); # return the root's a and b	
}

#(the old method) count total dominating sets (TDSs) in a distance-hereditary graph
sub TDSX {
	my (@TDSa,@TDSb,@TDSd,@TDSc, $TDSa, $TDSb, $TDSd, $TDSc, $i, $j);
	@post_order=(); # reset
	&post_order_traversal($dtree);
	foreach $node (@post_order){
		$k=$node->getUID;
		if ($node->isLeaf){	
			$TDSa1[$k]=0;
			$TDSa0[$k]=1;
			$TDSb[$k]=0;
			$TDSc[$k]=0;				
			$TDSd[$k]=1;  # check!!!			
		}else{
			$i=$node->getLeft->getUID;
			$j=$node->getRight->getUID;
			$op=$node->getNodeValue;	
			if($op eq 'F'){# op = false twin
				$TDSa1[$k]=$TDSa1[$i]*$TDSb[$j]+$TDSb[$i]*$TDSa1[$j]+$TDSa1[$i]*$TDSa1[$j]; 			
				$TDSa0[$k]=$TDSa0[$i]*$TDSb[$j]+$TDSb[$i]*$TDSa0[$j]+$TDSa0[$i]*$TDSa0[$j]+$TDSa0[$i]*$TDSa1[$j]+$TDSa1[$i]*$TDSa0[$j]; 
				$TDSb[$k]=$TDSb[$i]*$TDSb[$j];		
				$TDSc[$k]=$TDSc[$i]*($TDSa[$j]+$TDSb[$j]+$TDSd[$j]) + $TDSc[$j]*($TDSa[$i]+$TDSb[$i]+$TDSd[$i])
							+ $TDSc[$i]*$TDSc[$j] + $TDSa[$i]*$TDSd[$j] + $TDSd[$i]*$TDSa[$j];			
				$TDSd[$k]=$TDSb[$i]*$TDSd[$j]+$TDSd[$i]*$TDSb[$j]+$TDSd[$i]*$TDSd[$j];											
			}elsif($op eq 'T'){# op = true twin
				$TDSa1[$k]=$TDSa1[$i]*($TDSb[$j]+$TDSd[$j])+($TDSb[$i]+$TDSd[$i])*$TDSa1[$j]+($TDSa[$i]+$TDSc[$i])*($TDSa[$j]+$TDSc[$j]);
				$TDSa0[$k]=$TDSa0[$i]*($TDSb[$j]+$TDSd[$j])+($TDSb[$i]+$TDSd[$i])*$TDSa0[$j];									
				$TDSb[$k]=$TDSb[$i]*$TDSb[$j];			
				$TDSc[$k]=$TDSc[$i]*($TDSb[$j]+$TDSd[$j])+ ($TDSb[$i]+$TDSd[$i])*$TDSc[$j];			
				$TDSd[$k]=$TDSb[$i]*$TDSd[$j]+$TDSd[$i]*$TDSb[$j]+$TDSd[$i]*$TDSd[$j];						
			}else{# op = pendant      			
				$TDSa1[$k]=($TDSa[$i]+$TDSc[$i])*($TDSa[$j]+$TDSc[$j]) + $TDSa1[$i]*($TDSb[$j]+$TDSd[$j]);			
				$TDSa0[$k]=$TDSa0[$i]*($TDSb[$j]+$TDSd[$j]);	
				$TDSb[$k]=$TDSb[$i]*($TDSa1[$j]+$TDSb[$j])+ $TDSd[$i]*$TDSa1[$j];
				$TDSc[$k]=$TDSc[$i]*($TDSb[$j]+$TDSd[$j]);			
				$TDSd[$k]=$TDSd[$i]*$TDSb[$j];
			}
		} # else not leaf
		$TDSa[$k]=$TDSa1[$k]+$TDSa0[$k];		
	}	# foreach	
	return($TDSa1[$k]+$TDSb[$k]);	
}

# count connected dominating sets (CDSs) in a distance-hereditary graph
sub CDS {
	my (@w,@x,@y,@z,@e, $i, $j,$k,$op);
	
	@post_order=(); # reset
	&post_order_traversal($dtree);
	foreach $node (@post_order){
		$k=$node->getUID;
		if ($node->isLeaf){	
			$w[$k]=1;
			$x[$k]=0;					
			$y[$k]=0;
			$z[$k]=0;
			$e[$k]=1; 
		}else{
			$i=$node->getLeft->getUID;
			$j=$node->getRight->getUID;
			$op=$node->getNodeValue;	
			if($op eq 'F'){# op = false twin
				$w[$k]=0;
				$x[$k]=$w[$i]*($w[$j]+$x[$j]) + $x[$i]*($w[$j]+$x[$j]);				
				$y[$k]=0;				
				$z[$k]=$w[$i]*($z[$j]+$e[$j]) + $x[$i]*($z[$j]+$e[$j]) + $z[$i]*($w[$j]+$x[$j]+$z[$j]+$e[$j]) + $e[$i]*($w[$j]+$x[$j]+$z[$j]);
				$e[$k]=$e[$i]*$e[$j];				
			}elsif($op eq 'T'){# op = true twin				
				$w[$k]=$w[$i]*($w[$j]+$x[$j]+$z[$j]+$e[$j]) + $x[$i]*($w[$j]+$x[$j]+$z[$j]) + $z[$i]*($w[$j]+$x[$j]+$z[$j]) + $e[$i]*$w[$j];
				$x[$k]=$x[$i]*$e[$j] + $e[$i]*$x[$j];				
				$y[$k]=0;				
				#$y[$k]=$e[$i]*$x[$j]+$x[$i]*$e[$j];
				$z[$k]=$z[$i]*$e[$j] + $e[$i]*$z[$j];
				$e[$k]=$e[$i]*$e[$j];				
			}else{# op = pendant      			
				$w[$k]=$w[$i]*($w[$j]+$x[$j]+$z[$j]+$e[$j]) + $x[$i]*($w[$j]+$x[$j]+$z[$j])	+ $z[$i]*($w[$j]+$x[$j]+$z[$j]);
				$x[$k]=$x[$i]*$e[$j];				
				$y[$k]=$e[$i]*$w[$j];				
				$z[$k]=$z[$i]*$e[$j];				
				$e[$k]=0;
			}
		} # else not leaf		
	}	# foreach
	return($w[$k]+$y[$k]);
}


# count dominating sets (DSs) in a distance-hereditary graph
sub DS {
	my (@a,@b,@c,@d, $i, $j, $k, $op);
	@post_order=(); # reset
	&post_order_traversal($dtree);
	foreach $node (@post_order){
		$k=$node->getUID;
		if ($node->isLeaf){
			$a[$k]=1;
			$b[$k]=0;
			$c[$k]=0;
			$d[$k]=1;			
		} else {
			$i=$node->getLeft->getUID;
			$j=$node->getRight->getUID;
			$op=$node->getNodeValue;	
			if($op eq 'F'){# op = false twin
				$a[$k]=$a[$i]*($a[$j]+$b[$j]) + $b[$i]*$a[$j];
				$b[$k]=$b[$i]*$b[$j];
				$c[$k]=$a[$i]*($c[$j]+$d[$j]) + $b[$i]*$c[$j] + $c[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $d[$i]*($a[$j]+$c[$j]); 
				$d[$k]=$b[$i]*$d[$j] + $d[$i]*($b[$j]+$d[$j]); 
			}elsif($op eq 'T'){# op = true twin
				$a[$k]=$a[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $b[$i]*$a[$j] + $c[$i]*($a[$j]+$c[$j]) + $d[$i]*$a[$j]; 
				$b[$k]=$b[$i]*$b[$j];
				$c[$k]=$b[$i]*$c[$j] + $c[$i]*($b[$j]+$d[$j]) + $d[$i]*$c[$j]; 
				$d[$k]=$b[$i]*$d[$j] + $d[$i]*($b[$j]+$d[$j]); 
			}else{# op = pendant      
				$a[$k]=$a[$i]*($a[$j]+$b[$j]+$c[$j]+$d[$j]) + $c[$i]*($a[$j]+$c[$j]);				
				$b[$k]=$b[$i]*($a[$j]+$b[$j]) + $d[$i]*$a[$j]; 
				$c[$k]=$c[$i]*($b[$j]+$d[$j]);				
				$d[$k]=$d[$i]*$b[$j]; 				
			}	# else	op = pendant
		}	#else not leaf
	} # foreach node		
	return($a[$k]+$b[$k]); # return the root's a and b	
}

#create a random distance-hereditary graph
sub new_g {
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);

	@op=();
	@twin=();
	
	$op[2]='P'; # default P: add a new pendant vertex 2 to vertex 1 (or T truth twins op)
	$twin[2]=1;
	$g->add_edges([1,2]);
	#       0  1  2  3  4  5  6  7  8
	#@twin=('','', 1, 1, 2, 1, 5, 4, 7);
	#@op= ('','','P', 'F', 'P', 'T', 'T', 'T', 'F');
	for ($v=3; $v <=$n ; $v++){
		$u=int(rand($v-1))+1;#range [1..v-1]
		$twin[$v]=$u;
		#$u=$twin[$v];   #debug
		$r=rand(1);
		if ($r < $p1/($p1+$p2+$p3)){ # pendant op
		#if ($op[$v] eq 'P'){ #debug
			$op[$v]='P';			
			$g->add_edges([$v,$u]);
		}elsif ( $r < ($p1+$p2)/($p1+$p2+$p3)){ # false twins op
		#}elsif ($op[$v] eq 'F'){ #debug
			$op[$v]='F';			
			foreach $w ( $g->neighbours($u)){
				$g->add_edges([$v,$w]);	
			}			
		}else{# true twins op
		#}else{ #debug
			$op[$v]='T';
			foreach $w ( $g->neighbours($u)){
				$g->add_edges([$v,$w]);	
			}			
			$g->add_edges([$v,$u]);
		}
	}# for v
}

#---------------------------------------------------------------------
sub construct_decomposition_tree{
	my $i,$j,$ltree,$rtree,$root;
	my @tree=(),$uid=0;
	
	for ($j=$n ; $j>=2 ;$j--){	  
		$i=$twin[$j];
		if ( !$tree[$i]){ # there is no leave node labeled with vertex j
			$ltree=Tree::Binary -> new($i);
			$ltree->setUID(++$uid);
		}else{
			$ltree=$tree[$i];
		}
		if ( !$tree[$j]){
			$rtree=Tree::Binary -> new($j);			
			$rtree->setUID(++$uid);			
		}else{
			$rtree=$tree[$j];
		}
		
		$root=Tree::Binary -> new($op[$j]);
		$root->setUID(++$uid);
		$root->setLeft($ltree);
		$root->setRight($rtree);
		
		$tree[$i]=$root;
		
	} # for j	
	return($root);
}

#-------------------------------
sub print_decomposition_tree {
	my ($tree)=@_;     
	return if (!$tree); # null node 
	print "\t" x $tree -> getDepth, $tree -> getNodeValue, "\n";
	&print_decomposition_tree($tree->getRight);
	&print_decomposition_tree($tree->getLeft);
}
#-------------------------------
sub post_order_traversal{
  my ($t)=@_;     
  return if (!$t); # null node  
	&post_order_traversal($t->getLeft); 
	&post_order_traversal($t->getRight);   
  push(@post_order,$t); 
}# end of post_order_traversal
  

sub brute_force { # working for a multi-graph

	$max=2**$g->vertices-1;	
	@is_set = map { Set::Scalar->new() } 0..$max;

	$nds=0; # for counting dominating sets
	$ncds=0;# for counting connected dominating sets
	$ntds=0;# for counting total dominating sets
	
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );		
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		
		$dominating_vertices= Set::Scalar->new;  # for counting dominating sets
		$total_dominating_vertices= Set::Scalar->new;  # for counting total dominating sets		
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];		
					$dominating_vertices->insert($$a[0],$$a[1]);# for counting dominating sets
					if ($$a[0] == $vs ){
						$total_dominating_vertices->insert($$a[1]);# for counting total dominating sets
					}else{
						$total_dominating_vertices->insert($$a[0]);# for counting total dominating sets
					}					
				}  
				$is_set[$num]->insert($vs);
			}
		}
				
		if ($dominating_vertices->size == scalar($g->vertices)){ # for counting dominating sets
		  $nds++; 			
			#check if it is a connected dominating set			
			@dv = $is_set[$num]->elements;		#for counting connected dominating sets
			my $induced_subgraph = $g->subgraph(\@dv);      #for counting connected dominating sets
			if ($induced_subgraph->is_connected){           #for counting connected dominating sets
			  $ncds++;  				#for counting connected dominating sets				
			}                                       #for counting connected dominating sets			
			
			#check if it is a total dominating set			
			if ($total_dominating_vertices->size == scalar($g->vertices)){ # for counting total dominating sets
				$ntds++;
			}
		}				
	} # foreach num
	
	return($nds,$ncds,$ntds); 
}
