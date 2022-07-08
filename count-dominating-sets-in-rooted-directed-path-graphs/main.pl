#!/usr/bin/perl
# 
# count dominating sets in a rooted directed path graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Tree::Simple;
use Tree::Binary;
use Graph::Undirected;
$|=1;
#globals
$max_node_size=4;# clique tree: maximum vertices in the root node
$max_children=4;# clique tree: maximum children for each clique node
$max_depth=3;# clique tree: maximum depth
$max_extra=2;# clique tree: maximum new vertices in each clique node
$max_from_parent=2;# clique tree: maximum vertices that are inherent from the parent node
$g = Graph::Undirected->new(); # the rooted directed path graph
%order=();
@post_order=();

while ( $test < 2000){ # test 2000 random instances	  
	$kr=&create_clique_tree(); # create the corresponding clique tree of a random rooted directed path graph	
	#&print_clique_tree($kr);		
	&construct_graph($kr); # transfer the clique tree to the rooted directed path graph	
	next if (scalar($g->vertices) > 13);	 # due to the limitation of the brute-force method		
	print "\n=== test$test: |V|=",scalar($g->vertices), " and |E|=",scalar($g->edges),"\n";
	print "graph: $g\n";	
	$kr=&transfer_binary_clique_tree($kr);	
	print "our proposed algorithm 1:  ";	
	$DS1=Count_DS($kr);	
	print "#DS=$DS1\n";	
	print "the brute-force algorithm: ";			
	$DS2=&brute_force();
	print "#DS=$DS2\n";  
	$test++;
	if ($DS1 != $DS2){
		print "An error occured. Stop!\n";
		exit;
	}		
	$kr->DESTROY();
}
print "\n Tests completed successfully.\n";

# count dominating sets (DSs) in a rooted directed path graph
sub Count_DS {
	my ($kr)=@_;		
	my (@A,@B,@C, $i, $j, $k, $x, $y);	
	# reset A, B, C
	@A=();@B=(); @C=(); # assume all initial values are zero
	@post_order=(); # reset
	&post_order_traversal($kr);
	foreach $node (@post_order){
		$k=$node->getUID;		
		if ($node->isLeaf){
			$v=($node->getNodeValue()->elements)[0];				
			$A[$k]{$v}=1;
			$B[$k]{$v}=1;
			$C[$k]=0;	
		} else {			
			$Vk=$node->getNodeValue;			
			foreach $v ($Vk->elements){
				if ( $node->getChild(0)->getNodeValue->has($v)){
					$i=$node->getChild(0)->getUID;
					$j=$node->getChild(1)->getUID;
					$Vi=$node->getChild(0)->getNodeValue;
					$Vj=$node->getChild(1)->getNodeValue;
				}else{
					$i=$node->getChild(1)->getUID;
					$j=$node->getChild(0)->getUID;					
					$Vi=$node->getChild(1)->getNodeValue;
					$Vj=$node->getChild(0)->getNodeValue;
				}		
				#-- compute A[$k]{$v}
				$sum=$C[$j];	
				#foreach $u ( $Vj->intersection($Vk)->elements ){
				foreach $u ( $Vj->elements ){
					if ($order{$u} < $order{$v}){
						$sum += $A[$j]{$u};
					}						
				}	
				foreach $u ( $Vj->intersection($Vk)->elements ){
					$sum += $B[$j]{$u};
				}	
				$A[$k]{$v} = $A[$i]{$v} * $sum;
				
				#-- compute B[$k]{$v}
				$sum=$C[$j];	
				foreach $u ( $Vj->intersection($Vk)->elements ){
					if ($order{$u} > $order{$v}){
						$sum += $B[$j]{$u};
					}	
				}
				foreach $u ( $Vj->difference($Vk)->elements ){					
					$sum += $A[$j]{$u};
				}					
				$B[$k]{$v} = $B[$i]{$v} * $sum;
			} # for each $v in V(k)
			#-- compute C[$k]
			$sum1=$C[$i];
			foreach $u ( $Vi->difference($Vk)->elements ){
				$sum1 += $A[$i]{$u};
			}
			$sum2=$C[$j];
			foreach $u ( $Vj->difference($Vk)->elements ){
				$sum2 += $A[$j]{$u};
			}
			$C[$k]=$sum1*$sum2;
		} #else	
	} # foreach	node k
	$DS=$C[1];
	foreach $v ($kr->getNodeValue()->elements){
		$DS += $A[1]{$v};
	}	
	return($DS);
}

sub post_order_traversal{
	my ($k)=@_;	
	return if (!$k); # null node  	
	foreach my $ki ($k->getAllChildren()){
		&post_order_traversal($ki); 	
	}	
	push(@post_order,$k); 
}# end of post_order_traversal

sub create_clique_tree {
	my($uid, $n, $kr,$k, $child, $ksize, $endflag, $i, $j, $extra, $fps, $fp, @queue, @knode_member, @kinode_member);
	$uid=0; # the clique node id;	
	$n=int(rand($max_node_size))+1; # 1 ~ $max_node_size 
	$kr = Tree::Simple->new(Set::Scalar->new(1..$n));
	push(@queue,$kr);
	while ($k=shift(@queue)){
		next if ( $k->getDepth() == $max_depth );
		$child=int(rand($max_children+1)); # 0~ $max_children	
		@knode_member=$k->getNodeValue()->elements();
		$ksize=$k->getNodeValue()->size();			
		$endflag=0; $i=0;    
		$fps=0; # the number of vertices of all children that are derived from their parent
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
				$extra=int(rand($max_extra))+1;
				for ($j=0; $j < $extra ; $j++){
					push(@kinode_member,++$n);
				}  
				$ki=Tree::Simple->new(Set::Scalar->new(@kinode_member),$k);				
				push(@queue,$ki);
			}
			$i++; # next child
		}
	}
	return($kr);
}

sub transfer_binary_clique_tree {
	my ($kr)=@_;	
	my (@queue, $k, $vk, $vki, $ki, $endv, $v, $kChild, %parent, $kParent, $uid, @kis, $unionValues, $kx2, $kx, @path_len, $sn, $v);
	#print "Step 0:----\n";
	#&print_clique_tree($kr);	
	#-- Step 1: extend the leaf node for every vertex
	push(@queue,$kr);	
	while ($k=shift(@queue)){ # level-order traversal	
		$vk=$k->getNodeValue;
		$vki = Set::Scalar->new;
		foreach $ki ($k->getAllChildren()){
			push(@queue,$ki);
			$vki = $vki + $ki->getNodeValue;
		}		
		$endv=$vk-$vki; #endv is the set of vertices that end in node k
		next if ($endv->size ==1 && $k->isLeaf);
		foreach $v ( $endv->elements){ 
			Tree::Simple->new(Set::Scalar->new($v),$k); #attach a leaf node containg v to node k
		}
	}
	#print"step 1: after extending the leaf node---\n";
	#&print_clique_tree($kr);	
	#-- Step 2: remove the nodes of degree 1
	@queue=();
	while ( $kr->getChildCount == 1) { # remove the root if it is degree 1
		$kr=$kr->getChild(0);
	}	
	$kr = $kr->clone;	# set the new root node
	#record the parent of each node(Tree::Simple module; getParent() bug??)
	%parent=();
	push(@queue,$kr);	
	while ($k=shift(@queue)){ # level-order traversal		
		push(@queue,$k->getAllChildren);
		$parent{$k->getUID}=$k->getParent();
	}	
	#remove the internal nodes of degree 1
	push(@queue,$kr);	
	while ($k=shift(@queue)){ # level-order traversal		
		push(@queue,$k->getAllChildren);
		if ($k->getChildCount == 1){	
			$kChild=$k->getChild(0);
			$kParent=$parent{$k->getUID};										
			$kParent->removeChild($k);			
			$kParent->addChild($kChild);
			$parent{$kChild->getUID}=$kParent; 			
		}
	}
	#print"step 2: after removing degree-1 nodes ---\n";
	#&print_clique_tree($kr);	
	#-- Step 3: transfer into an equivalent binary clique tree and set the uid for each node
	$uid=1;
	@queue=();		
	push(@queue,$kr);	
	while ($k=shift(@queue)){ # level-order traversal				
		$k->setUID($uid++);				
		@kis=$k->getAllChildren();		
		next if (scalar(@kis) < 2);		
		push(@queue,@kis);						
		$unionValues = Set::Scalar->new;
		$kx=$k;
		for ($i=0; $i < scalar(@kis)-2 ; $i++){			
			$k->removeChild($kis[$i]);
			$kx->addChild($kis[$i]); # the first child
			
			$unionValues += $kis[$i]->getNodeValue;			
			$kx2=Tree::Simple->new($k->getNodeValue - $unionValues);  # kx2 will be the child of kx
			$kx2->setUID($uid++);
			$kx->addChild($kx2); # the second child
			
			$kx=$kx2;
		}
		# add the last two children		
		$k->removeChild($kis[$i]);
		$kx->addChild($kis[$i]); # the first child		
		$k->removeChild($kis[$i+1]);
		$kx->addChild($kis[$i+1]); # the second child
	}
	#print"step 3: after spliting each node of out-degree of d > 2 into d-1 nodes of out-degree of 2 ---\n";
	#&print_clique_tree($kr);
	@path_len=();	
	#-- Step 4: topological sort for each vertex according to its starting node in the tree (decending from root to leaves)
	$sn=scalar($g->vertices); %order=();
	push(@queue,$kr);		
	while ($k=shift(@queue)){ # level-order traversal		
		push(@queue,$k->getAllChildren());				
		foreach $v ($k->getNodeValue()->elements){
			if ( ! exists $order{$v} ){ # the first visit to v
				$order{$v}=$sn--;				
			}			
		}
	}
	return($kr)
}

sub construct_graph {
	my ($root)=@_;
	$g = Graph::Undirected->new();
	&construct_graph_by_dfs($root);
}

sub construct_graph_by_dfs{ #depth first search 
	my ($t)=@_;  
	my ($c,$s,@elements,$i,$j);
	return if (!$t);
	foreach $c ($t->getAllChildren()){
		&construct_graph_by_dfs($c); 
	} 
	$s=$t->getNodeValue();
	@elements=$s->elements; 
	# all vertices in clique node t are connected to each other
	for ($i=0; $i < $s->size - 1; $i++){
		for ($j=$i+1; $j < $s->size ; $j++){    
			$g->add_edge($elements[$i], $elements[$j]);
		}
	}	
}

# brute force algorithm
sub brute_force {
	my($max, $nds, $num, $bits, @bit, $vs, $dominating_vertices, @edges, $a, $edge);
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
		if ($dominating_vertices->size == scalar($g->vertices)){ # for counting dominating sets
		  $nds++; 			
		}				
	} # foreach num	
	return($nds); 
}

sub print_clique_tree{
	my($tree)=@_;		
	print "|V|=",scalar($g->vertices), " and |E|=",scalar($g->edges),"\n";
	print "root=",$tree->getNodeValue(),":",$tree->getUID,"\n";
	$tree->traverse(sub {
		my ($_tree) = @_;
	    print (("\t" x ($_tree->getDepth()+1)), $_tree->getNodeValue(),":",$_tree->getUID,"\n");
	});
	print "\n";
}
