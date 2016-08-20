#!/usr/bin/perl
# 
# count maximal independent sets (MIS) in a rooted directed path graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Tree::Simple;
use Graph;
$|=1;

#globals
$max_node_size=3;# clique tree: maximum vertices in the root node
$max_children=2;# clique tree: maximum children for each clique node
$max_depth=3;# clique tree: maximum depth
$max_extra=2;# clique tree: maximum new vertices in each clique node
$max_from_parent=2;# clique tree: maximum vertices that are inherent from the parent node
$g = Graph::Undirected->new(); # the rooted directed path graph
	
while ( $test++ < 20 ){ # test 20 random instances	  
	$kr=&create_clique_tree(); # create the corresponding clique tree of a random rooted directed path graph
	&construct_graph($kr); # transfer the clique tree to the rooted directed path graph

	print "\n== test$test: the clique-trees: ==\n";	
	&print_clique_tree($kr);	

	print "our proposed algorithm:    ";	
	$mis1=Count_MIS($kr);
	print "#MIS=$mis1\n";
	
	print "the brute-force algorithm: ";		
	$mis2=&brute_force();
	print "#MIS=$mis2\n";
  
  if ($mis2!='' && $mis1 != $mis2){
		print "An error occured. Stop!\n";
		exit;
	}
	$kr->DESTROY();
}
print "\n Tests completed successfully.\n";


sub Count_MIS {
	@nmisv=();
	@nxmis=();
	#Add a dummy clique k0 as the parent of kr in T
	$k0 = Tree::Simple->new(Set::Scalar->new()); #empty set
	$k0->setUID(1);
	$k0->addChild($kr);
	&COUNT($kr);  ##
	return($nxmis[$kr->getUID][$k0->getUID]);
}

sub COUNT {
	my ($k)=@_;
	
	if ($k->isLeaf){
		foreach $v ($k->getNodeValue->elements){
			$nmisv[$k->getUID][$v]=1;
		}
		for($d=$k; !$d->isRoot ; $d=$d->getParent  ){
			$nxmis[$k->getUID][$d->getParent->getUID]=($k->getNodeValue - $k->getParent->getNodeValue)->size;
		}  
	}else{# $k is not leaf node
		foreach $ki ($k->getAllChildren()){
			&COUNT($ki);
		}   
		foreach $v ($k->getNodeValue->elements){
			$nmisv[$k->getUID][$v]=1;
			foreach $ki ($k->getAllChildren()){
				if ( $ki->getNodeValue->has($v) ){
					$nmisv[$k->getUID][$v] *= $nmisv[$ki->getUID][$v];
				}else{
					$nmisv[$k->getUID][$v] *= $nxmis[$ki->getUID][$k->getUID];
				}
			}
		}
		
		$sum=0;
		foreach $v (($k->getNodeValue - $k->getParent->getNodeValue())->elements){
			$sum += $nmisv[$k->getUID][$v];
		}
		
		$S=Set::Scalar->new();
		foreach $ki ($k->getAllChildren()){   
			$S += $ki->getNodeValue;
		}
		
		for($d=$k; !$d->isRoot ; $d=$d->getParent  ){
			$nxmis[$k->getUID][$d->getParent->getUID]=$sum;			
			if ( ($k->getNodeValue - $d->getParent->getNodeValue) <= $S){
				$tmp=1;
				foreach $ki ($k->getAllChildren()){ 
					$tmp *= $nxmis[$ki->getUID][$d->getParent->getUID];
				}
				$nxmis[$k->getUID][$d->getParent->getUID] += $tmp;
			}
		}
	}
}

sub create_clique_tree {
	$uid=1; # the clique node id;
  my($i,$n,$s,$j,$child,$fp,$fps,$k,$ki,$ksize,@queue,@knode_member, @kinode_member);
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

sub construct_graph {
	my ($root)=@_;
	$g = Graph::Undirected->new();
	&dfs($root);
}

#depth first search 
sub dfs{
	my ($t)=@_;  
	my ($c,$s,@elements,$i,$j);
	return if (!$t);
	foreach $c ($t->getAllChildren()){
		&dfs($c); 
	} 
  
	$s=$t->getNodeValue();
	@elements=$s->elements; 
	# all vertices in clique node s are connected to each other
	for ($i=0; $i < $s->size - 1; $i++){
		for ($j=$i+1; $j < $s->size ; $j++){    
			$g->add_edge($elements[$i], $elements[$j]);
		}
	}	
}

# brute force algorithm
sub brute_force {	
  return("") if ( scalar($g->vertices) > 16); 
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
	return($mvc);# Note: the number of minimal vertex covers = the number of maximal indpendent sets
}

sub print_clique_tree{
  my($tree)=@_;		
	
	print "|V|=",scalar($g->vertices), " and |E|=",scalar($g->edges),"\n";
  print "root=",$tree->getNodeValue(),"\n";
  $tree->traverse(sub {
      my ($_tree) = @_;
      print (("\t" x ($_tree->getDepth()+1)), $_tree->getNodeValue(), "\n");
  });
	print "\n";
}
