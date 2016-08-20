#!/usr/bin/perl
#
#  Compute the k-terminal reliability of a rooted directed path graph
#
#  by Min-Sheng Lin
#
use Set::Scalar;  # For Set data structure
use Tree::Simple; # for tree data structure
use Graph;        # for graph data structure
$|=1;

#globals
$max_node_size=3;# clique tree: maximum vertices in the root node
$max_children=2;# clique tree: maximum children for each clique node
$max_depth=3;# clique tree: maximum depth
$max_extra=2;# clique tree: maximum new vertices in each clique node
$max_from_parent=2;# clique tree: maximum vertices that are inherent from the parent node
$g = Graph::Undirected->new(); # the rooted directed path graph
$kr=''; # the root node of the corresponding clique tree of g

$limit=13; # the limitation for brute-force method
$p=0.7;  # the operational probability for each vertex
$q=1-$p;

@k_set=();  # store the k target vertices
@k_tag=();  # store the tag whether v is in k_set
@reverse_oredr=();
@S=();  #S(i): set of vertices which start at node i; S(i)=v(i)- v(i+) 
@C=();  #C(v): set of clique nodes which contains vertex v
@PrEF=();
@PrEC=();

while ( $test++ < 20 ){ # test 20 random instances	  
	$kr=&create_clique_tree();  # set $kr ; the clique tree of a rooted directed path graph  
	&construct_graph($kr); # set $g; transfer the clique tree into the rooted directed path graph	
	
	print "\n== test$test: the clique-trees: ==\n";	
	&print_clique_tree($kr);

	print "our proposed algorithm:    ";	
	$ktr1=&Compute_KTR($kr);
	print "KTR=$ktr1\n";

	print "the brute-force algorithm: ";			
	$ktr2=&brute_force(); 
	print "KTR=$ktr2\n";	
	
	if ($ktr2 > 0 && ($ktr2-$ktr1 > 0.000001 || $ktr1-$ktr2 > 0.000001) ){
		print "An error occured. Stop!\n";
		exit;
	}	
	$kr->DESTROY();  
}
print "\n Tests completed successfully.\n";

sub Compute_KTR {
	@reverse_order=();	
	&post_order_travesal($kr);  # compute the sequence of reverse topological order and store it in @reverse_order;  
	
	@ancestor=();
	&find_ancestor($kr);# find the ancestors for each node, if A is a ancestor of B, then $ancestor[B][A]=1 for all A,B in the clique tree
	
	@S=();
	@C=();
	&compute_S_C(); # compute S set and C set
		
	@PrEF=();
	&Compute_PrEF();
		
	@PrEC=();
	&Compute_PrEC();
		
	$ktr=1;
	$x=&Compute_LCA();
	foreach $xx ($x->getAllChildren()){
		$ktr *= $PrEC[$kr->getUID][$xx->getUID];
	}	 
	return($ktr);
} 

sub post_order_travesal{
	my($t)=@_;     
	my($c);
	return if (!$t); # null node
	foreach $c ($t->getAllChildren()){
		&post_order_travesal($c); 
	}
	push(@reverse_order,$t); 
}

sub find_ancestor {
	($kr)=@_;
	$kr->traverse(sub {
			my ($kx) = @_;
			my $ky;
			for($ky=$kx; !$ky->isRoot ; $ky=$ky->getParent  ){	  
				$ancestor[$kx->getUID][$ky->getParent->getUID]=1; # tag: y is the ancestor of x
			} 
		}); # end of traverse
}  

# compute S(i) and C(v)	
sub compute_S_C {	
	#S(i):set of vertices which start at node i ; Note: vertex v in S(i) iff v in V(i) and v not in V(i+)
	#C(v):set of clique nodes which contain vertex v
	
	#compute S(i);					
	$S[$kr->getUID]= Set::Scalar->new;
	$S[$kr->getUID]= $kr->getNodeValue; # initial value for root node; S(r)=v(r)
	$kr->traverse(sub { #Note:root kr will not be traversed root since traversing begin from kr->child
			my ($k) = @_;
			$S[$k->getUID]= Set::Scalar->new;  
			my $k2=$k->getParent;
			$S[$k->getUID]=$k->getNodeValue - $k2->getNodeValue; # S(k) = v(k) - v(k+)
		}); # end of traverse 
  
	#compute C(v)
	foreach $v ($g->vertices){
		$C[$v]= Set::Scalar->new; 
	}
	foreach $v ($kr->getNodeValue->elements){ # foreach v in V(r)
		$C[$v] +=  $kr->getUID ; 
	}	
	$kr->traverse(sub { #Note:root kr will not be traversed root since traversing begin from kr->child
		my ($k) = @_;	 
		foreach $v ($k->getNodeValue()->elements()){ # foreach v in V(k)
			$C[$v] +=  $k->getUID ; 
		}			
	}); # end of traverse
}

sub Compute_PrEF {  # refer to our paper (new version)   
	for $kk (0 .. $#reverse_order) {  
		$k=$reverse_order[$kk]; # the clique node k in the tree
		$kUID=$k->getUID;
		$PrEF[$kUID][$kUID]=1; # initial condition  PrEF(k,k)=1;
	}
	for $kk (0 .. $#reverse_order-1) { # for k in T(r)-r in reverse topological order (it must be in the reverse order)
		$k=$reverse_order[$kk];
		$kUID=$k->getUID;
		$k2UID=$k->getParent->getUID; # k2=k+ => denote the parent of k
		
		for $hh (0 .. $#reverse_order-1) { # (it is not necessary in the reverse order)
			$h=$reverse_order[$hh];
			$hUID=$h->getUID;
			if ( $kUID==$hUID || $ancestor[$hUID][$kUID] ){ # h in T(k) <=> h==k or k is the ancestor of h
				$PrEF[$k2UID][$hUID]=$PrEF[$kUID][$hUID];  # PrEF(k+,h)=PrEF(k,h)
			}
		}    
		foreach $v ($S[$k2UID]->elements){ # foreach v in s(k+)
			foreach $hUID ($C[$v]->elements){ # foreach node h in C(v)
				if ( $kUID==$hUID || $ancestor[$hUID][$kUID] ){ # if h is in T(k)
					$PrEF[$k2UID][$hUID]=$PrEF[$k2UID][$hUID]*$q[$v];
				}
			}
		}
	}
}

sub Compute_PrEC {
	for $kk (0 .. $#reverse_order) { # for k in T(r) in reverse topological order
		$k=$reverse_order[$kk];
		$kUID=$k->getUID;
		for $hh (0 .. $#reverse_order) { # for h in T(k)-k in reverse topological order
			$h=$reverse_order[$hh];
			$hUID=$h->getUID;
			if ( $ancestor[$hUID][$kUID] ){ # h in T(k)-k ==>  k is the ancestor of h
				if ($h->isLeaf){
					$PrEC[$kUID][$hUID]=1-$PrEF[$kUID][$hUID];   		  
				}else{   
					my $rtmp1=1;
					my $rtmp2=1;
					foreach $hx ($h->getAllChildren()){
						$hxUID=$hx->getUID;
						$rtmp1 *= $PrEC[$kUID][$hxUID];
						$rtmp2 *= $PrEC[$hUID][$hxUID];
					}
					$PrEC[$kUID][$hUID]=$rtmp1 - $PrEF[$kUID][$hUID]*$rtmp2;
				}
			}
		}
	}
}

sub Compute_LCA {
	#find the target cliques which contain some target vertices  
	$k_clique_set=Set::Scalar->new(); 
	$dummyrootnode = Tree::Simple->new();
	$dummyrootnode->addChild($kr); # note: since the traverse-sub begins from its children, we add this dummy node 
	$dummyrootnode->traverse(sub { # the traversing will begin from its child => kr
			my ($_tree) = @_;
			foreach my $v ($_tree->getNodeValue()->elements){
				if ($k_tag[$v]){
					$k_clique_set->insert($_tree);
					break;
				}
			}
		});		
	return(0) if ($k_clique_set->is_empty);
	
	#find the LCA of target cliques nodes  
	@k_clique_set=$k_clique_set->elements;	
	$klca=pop @k_clique_set;    
	while (($kx=pop @k_clique_set)){      
		$klca=&LCA($klca, $kx);
	}  
	return($klca);
}

sub LCA {
	my ($kx, $ky)=@_;
	return $ky if (($kx->getUID == $ky->getUID) || $ancestor[$kx->getUID][$ky->getUID] );  
	return ( &LCA($ky->getParent, $kx) );
}

sub create_clique_tree {
	$uid=1; # the clique node id;	
	$n=int(rand($max_node_size))+1; # 1 ~ $max_node_size 
	$kr = Tree::Simple->new(Set::Scalar->new(1..$n));
	$kr->setUID(++$uid);
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
				$ki->setUID(++$uid);
				push(@queue,$ki);
			}
			$i++; # next child
		}
	}
	return($kr);
}

# construct the corresponding rooted directed path graph g
sub construct_graph{ 
	my ($root)=@_;

	@k_tag=();  # reset k target vertices
	@k_set=();  
	$g = Graph::Undirected->new();
	&dfs($root);  # construct the corresponding graph g and tag the k target vertices 

	foreach $v ($g->vertices){  # set the operational probability for each vertices
		if ($k_tag[$v] ){ # v is a target vertex
			$p[$v]=1;
			$q[$v]=0;
		}else{# v is not a target vertex
			$p[$v]=$p;
			$q[$v]=1-$p;	
		}	
	}
}

# depth first search  
sub dfs{
	my ($t)=@_;  
	my ($i, $j, $c,$s,@elements, $diff);
	return if (!$t); # null node
	foreach $c ($t->getAllChildren()){
		&dfs($c); 
	} 
  
	$tset=$t->getNodeValue();
	@elements=$tset->elements;
	$g->add_vertices(@elements);
	# all vertices in clique node t are connected to each other	
	for ($i=0; $i < $tset->size - 1; $i++){
		for ($j=$i+1; $j < $tset->size ; $j++){    
			$g->add_edge($elements[$i], $elements[$j]);
		}
	}	
	#check if t is a leaf node
	if ( $t->isLeaf){
		if ($t->isRoot){
			$diff=$tset; # if root is a leaf node (only one root node), all vertices in root are k target nodes
		}else{   
			my $t2set=$t->getParent->getNodeValue();
			$diff=$tset-$t2set;  # diff denotes the vertices in t but not in the parent of t
		}  
		for my $v ($diff->elements){ # let the vertices in a leaf node but not in its parent node be K-target nodes
			$k_tag[$v]=1;  # mark v being a target vertex
			push(@k_set,$v);
		}	
	}
}

sub brute_force {
	$n=$g->vertices;
	if ($n > $limit){
		return("");
	}   
	$max=2**$n-1;
	$ktr=0;
	foreach $i (0..$max){
		$h = $g->copy_graph;
		$used_1[1];  
		$bits = unpack ( "B*", pack("N",$i) );		
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		$pr=1;
		
		foreach $v ($h->vertices){  
			$px=$p[$v];
			if ($bit[$v-1] == 1){ # v is working	
				$pr=$pr*$px;
			}else{ # v is failed
				$pr=$pr*(1-$px);
				$h->delete_vertex($v);
			}
			break if ($pr==0);
		}

		next if ($pr==0);  # some of target vertices fail 
		if ($h->same_connected_components(@k_set)){
			$ktr += $pr;
		}    
	}
	return $ktr;
}

sub print_clique_tree{
	my($tree)=@_;		
	print "|V|=",scalar($g->vertices), ", |E|=",scalar($g->edges);
	print " and target vertices=@k_set\n";
	print "root=",$tree->getNodeValue(),"\n";
	$tree->traverse(sub {
		my ($_tree) = @_;
		print (("\t" x ($_tree->getDepth()+1)), $_tree->getNodeValue(), "\n");
	});
	print "\n";
}
