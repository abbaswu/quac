from typing import Any, Set, Tuple, List, Dict

import logging
import random
from collections import defaultdict
from overrides import overrides
from torch.nn.modules.container import Sequential
from torch.nn.modules.dropout import Dropout

import tqdm

from allennlp.common.file_utils import cached_path
from allennlp.data.dataset_readers.dataset_reader import DatasetReader
from allennlp.data.fields import TextField, ListField, MultiLabelField, SequenceLabelField, LabelField
from allennlp.data.instance import Instance
from allennlp.data.tokenizers import CharacterTokenizer
from allennlp.data.tokenizers.sentence_splitter import SentenceSplitter
from allennlp.data.token_indexers import SingleIdTokenIndexer, TokenIndexer
from allennlp.data import Token
from allennlp.common.util import JsonDict
from allennlp.predictors.predictor import Predictor
from typing import Dict

import logging
from overrides import overrides
import torch
from torch import nn
import numpy as np
from allennlp.data import Vocabulary
from allennlp.modules.seq2vec_encoders import CnnEncoder
from allennlp.models.model import Model
from allennlp.nn import util
from allennlp.training.metrics.average import Average
from allennlp.modules import TextFieldEmbedder

import logging
from overrides import overrides
import numpy as np
from numpy import ndarray, _DType
import torch
from torch import nn
from sklearn.metrics import precision_recall_curve
from allennlp.common.checks import ConfigurationError
from allennlp.training.metrics.metric import Metric

log = logging.getLogger(__name__)  # pylint: disable=invalid-name

NEGATIVE_RELATION_NAME = 'NA'
class RelationInstancesReader(DatasetReader):
    r"""DatasetReader to read a relation extraction dataset.

    Each example is a pair of entities, bag (list) of sentences and a relation type. The sentences of each
    bag should be listed consecutively in the dataset file.

    File format: tab separated text file of 7 columns. They are:
        entity1_id
        entity2_id
        entity1_text: can be NA because it is not used by the model
        entity2_text: can be NA because it is not used by the model
        relation_type: use NA to indicate No Relation
        sentence: entity mentions are highlighted with <e1>entity1<\e1> and <e2>entity2<\e2>
        supervision_type: "direct" or "distant"

    The reader assumes that the sentences relevant to a pair of entities are all listed consecutively.
    If the entity pair changes, the reader starts a new bag.

    """

    max_distance:int = 30  # for position embeddings
    max_sentence_length:int = 130 # words
    max_bag_size:int
    negative_exampels_percentage:int
    with_direct_supervision:bool
    _tokenizer:CharacterTokenizer
    _token_indexers: Dict[str,TokenIndexer]
    _inst_counts: Dict[str, int]  = defaultdict(int)  # count instances per relation type
    _pairs: Set[Tuple[str,str]] = set()  # keep track of pairs of entities
    _bag_sizes: Dict[int,int] = defaultdict(int)  # count relation types per bag
    _relation_coocur:  Dict[str, int] = defaultdict(int)  # count relation types per bag
    _failed_mentions_count: int = 0  # count mentions with wrong formating
    _count_direct_supervised_inst: int = 0
    _count_bag_labels: Dict[int, int] = defaultdict(int)
    def __init__(self, lazy = False,
                 max_bag_size = 25,
                 negative_exampels_percentage = 100,
                 with_direct_supervision = True):
        """
        args:
            lazy: lazy reading of the dataset
            max_bag_size: maximum number of sentences per a bag
            negative_exampels_percentage: percentage of negative examples to keep
            with_direct_supervision: keep or ignore direct supervision examples
        """
        super().__init__()
        self.max_bag_size = max_bag_size
        self.negative_exampels_percentage = negative_exampels_percentage
        self.with_direct_supervision = with_direct_supervision

        self._tokenizer = CharacterTokenizer()
        self._token_indexers = {"tokens": SingleIdTokenIndexer()}

        # for logging and input validation
        self._inst_counts = defaultdict(int)  # count instances per relation type
        self._pairs = set()  # keep track of pairs of entities
        self._bag_sizes = defaultdict(int)  # count relation types per bag
        self._relation_coocur = defaultdict(int)  # count relation types per bag
        self._failed_mentions_count: int = 0  # count mentions with wrong formating
        self._count_direct_supervised_inst: int = 0
        self._count_bag_labels = defaultdict(int)
    def _read(self, file_path):
        with open(cached_path(file_path), "r") as data_file:
            log.info("Reading instances from lines in file at: %s", file_path)

            self._inst_counts = defaultdict(int)  # count instances per relation type
            self._pairs = set()  # keep track of pairs of entities
            self._bag_sizes = defaultdict(int)  # count relation types per bag
            self._relation_coocur = defaultdict(int)  # count relation types per bag
            self._failed_mentions_count = 0
            self._count_direct_supervised_inst: int = 0
            self._count_bag_labels: Dict = defaultdict(int)
            e1 = None
            e2 = None
            rels = set()
            mentions = set()
            # Lines are assumed to be sorted by entity1/entity2/relation_type
            for _, line in enumerate(tqdm.tqdm(data_file.readlines())):
                line = line.strip()
                new_e1, new_e2, _, _, rel, m, supervision_type = line.strip().split("\t")
                assert supervision_type in ['direct', 'distant']
                if new_e1 != e1 or new_e2 != e2 or supervision_type == 'direct':
                    # new entity pair
                    if rels:
                        # subsample negative examples and sentence-level supervised examples
                        if random.randint(1, 100) <= self.negative_exampels_percentage or \
                           NEGATIVE_RELATION_NAME not in rels or \
                           supervision_type == 'direct':  # pylint: disable=unsupported-membership-test

                            if not self.with_direct_supervision and supervision_type == 'direct':
                                pass
                            else:
                                inst = self.text_to_instance(e1, e2, rels, mentions, is_predict=False,
                                                             supervision_type=supervision_type)
                                if inst:
                                    yield inst

                    e1 = new_e1
                    e2 = new_e2
                    rels = set([rel])
                    mentions = set([m])
                else:
                    # same pair of entities, just add the relation and the mention
                    rels.add(rel)
                    mentions.add(m)
            if rels:
                if not self.with_direct_supervision and supervision_type == 'direct':
                    pass
                else:
                    inst = self.text_to_instance(e1, e2, rels, mentions, is_predict=False, supervision_type=supervision_type)
                    if inst is not None:
                        yield inst

            # log relation types and number of instances
            for rel, cnt in sorted(self._inst_counts.items(), key=lambda x: -x[1]):
                log.info("%s - %d", rel, cnt)

            # log number of relations per bag
            log.info("number of relations per bag size (bagsize -> relation count)")
            for k, v in sorted(self._bag_sizes.items(), key=lambda x: -x[1]):
                log.info("%s - %d", k, v)

            for k, v in sorted(self._relation_coocur.items(), key=lambda x: -x[1]):
                log.info("%s - %d", k, v)

    def text_to_instance(self, e1, e2,  # pylint: disable=arguments-differ
                         rels,
                         mentions,
                         is_predict,
                         supervision_type):
        """Construct an instance given text input.

        is_predict: True if this is being called for prediction not training
        supervision_type: direct or distant

        """ 
        assert supervision_type in ['direct', 'distant']

        if (e1, e2) in self._pairs and supervision_type == 'distant' and not is_predict:
            assert False, "input file is not sorted, check entities %s, %s" % (e1, e2)
        self._pairs.add((e1, e2))

        for rel in rels:
            self._inst_counts[rel] += 1  # keep track of number of instances in each relation type for logging

        if NEGATIVE_RELATION_NAME in rels:
            if len(rels) > 1:
                log.error("Positive relations between entities can\'t include %s. "
                          "Found relation types: %s between entities %s and %s",
                          NEGATIVE_RELATION_NAME, rels, e1, e2)
            rels.remove(NEGATIVE_RELATION_NAME)

        self._bag_sizes[len(rels)] += 1
        if len(rels) > 1:
            rels_str = ", ".join(sorted(list(rels)))
            self._relation_coocur[rels_str] += 1

        filtered_mentions = list(mentions)[:self.max_bag_size]  # limit number of mentions per bag

        fields_list = []
        for m in filtered_mentions:
            try:
                mention_fields = self._tokens_distances_fields(
                        self._tokenizer.tokenize(m)[:self.max_sentence_length]
                )
                fields_list.append(mention_fields)
            except ValueError:
                # ignore mentions with wrong entity tags
                self._failed_mentions_count += 1
                if self._failed_mentions_count % 1000 == 0:
                    log.error('Number of failed mentions: %d', self._failed_mentions_count)

        if len(fields_list) == 0:
            return None  # instance with zero mentions (because all mentions failed)

        mention_f, position1_f, position2_f = zip(*fields_list)

        if len(rels) == 0:
            bag_label = 0  # negative bag
        elif supervision_type == 'direct':
            bag_label = 1  # positive bag with sentence-level supervision
        else:
            bag_label = 2  # positive bag distantly supervised

        self._count_bag_labels[bag_label] += 1
        sent_labels = [LabelField(bag_label, skip_indexing=True)] * len(fields_list)

        if supervision_type == 'direct':
            is_direct_supervision_bag_field = TextField(self._tokenizer.tokenize(". ."), self._token_indexers)
            self._count_direct_supervised_inst += 1
        else:
            is_direct_supervision_bag_field = TextField(self._tokenizer.tokenize("."), self._token_indexers)

        fields = {"mentions": ListField(list(mention_f)),
                  "positions1": ListField(list(position1_f)),
                  "positions2": ListField(list(position2_f)),
                  "is_direct_supervision_bag": is_direct_supervision_bag_field,
                  "sent_labels": ListField(sent_labels),  # 0: -ve, 1: directly supervised +ve, 2: distantly-supervised +ve
                  "labels": MultiLabelField(rels),  # bag-level labels
                 }
        return Instance(fields)
    def _tokens_distances_fields(self, tokens):
        """Returns the updated list of tokens and entity distances for the first and second entity as fields."""
        tokens, positions1, positions2 = self._tokens_distances(tokens)

        t_f = TextField(tokens, self._token_indexers)
        return 1,2,3
        # p1_f = SequenceLabelField(positions1, t_f)
        # p2_f = SequenceLabelField(positions2, t_f)
        # return t_f, p1_f, p2_f
    def _tokens_distances(self, tokens):
        e1_loc = []
        e2_loc = []

        while len(tokens) < 5:  # a hack to make sure all sentences are at least 5 tokens. CNN breaks otherwise.
            tokens.append(Token(text='.'))
        
        for i, token in enumerate(tokens):
            if token.text.startswith('<e1>'):
                e1_loc.append((i, 'start'))
                token.text = token.text[4:]
            if token.text.endswith('</e1>'):
                e1_loc.append((i, 'end'))
                token.text = token.text[:-5]
            if token.text.startswith('<e2>'):
                e2_loc.append((i, 'start'))
                token.text = token.text[4:]
            if token.text.endswith('</e2>'):
                e2_loc.append((i, 'end'))
                token.text = token.text[:-5]

        positions1 = self._positions(len(tokens), e1_loc)
        positions2 = self._positions(len(tokens), e2_loc)

        return tokens, positions1, positions2
    def _positions(self, tokens_count, e_loc):
        # if the entity tags are missing, return a list of -1's
        if not e_loc:
            raise ValueError('entity tags are missing.')
        prev_loc = (-10000000000, 'end')  # large negative number
        next_loc_index = 0
        next_loc = e_loc[next_loc_index]
        distance_list = []
        for i in range(tokens_count):
            if prev_loc[1] == 'end' and next_loc[1] == 'start':
                # between two entities
                to_min = [abs(i - prev_loc[0]), abs(i - next_loc[0])]
                to_min.append(self.max_distance)
                distance = min(to_min)
            elif prev_loc[1] == 'start' and next_loc[1] == 'end':
                # inside the same entity
                distance = 0
            else:
                # malformed e_loc
                distance = self.max_distance

            distance_list.append(distance)
            while i == next_loc[0]:
                prev_loc = next_loc
                next_loc_index += 1
                if next_loc_index >= len(e_loc):
                    next_loc = (10000000000, 'start')  # large positive number
                else:
                    next_loc = e_loc[next_loc_index]

        return distance_list
    
    
    
    # @overrides
 

    # @overrides


class CombDistDirectRelex(Model):
    num_classes:int
    text_field_embedder:TextFieldEmbedder
    dropout_weight:float
    with_entity_embeddings:bool
    sent_loss_weight:int
    attention_weight_fn:str
    attention_aggregation_fn:str
    pos_embed:nn.Embedding
    pos_embed_weights:np.ndarray
    cnn:CnnEncoder
    dropout:Dropout
    attention_ff:nn.Sequential
    ff_before_alpha:nn.Sequential
    ff:nn.Sequential
    loss:torch.nn.BCEWithLogitsLoss
    metrics:Dict[str, Metric]
    vocab:Vocabulary
    def __init__(self, vocab,
                 text_field_embedder,
                 cnn_size = 100,
                 dropout_weight = 0.1,
                 with_entity_embeddings = True ,
                 sent_loss_weight = 1,
                 attention_weight_fn = 'sigmoid',
                 attention_aggregation_fn = 'max'):
        regularizer = None
        super().__init__(vocab, regularizer)
        self.num_classes = self.vocab.get_vocab_size("labels")

        self.text_field_embedder = text_field_embedder
        self.dropout_weight = dropout_weight
        self.with_entity_embeddings = with_entity_embeddings
        self.sent_loss_weight = sent_loss_weight
        self.attention_weight_fn = attention_weight_fn
        self.attention_aggregation_fn = attention_aggregation_fn

        # instantiate position embedder
        pos_embed_output_size = 5
        pos_embed_input_size = 2
        self.pos_embed = nn.Embedding(pos_embed_input_size, pos_embed_output_size)
        pos_embed_weights = np.array([range(pos_embed_input_size)] * pos_embed_output_size)
        self.pos_embed.weight = nn.Parameter(torch.Tensor(pos_embed_weights))

        d = cnn_size
        sent_encoder = CnnEncoder  # TODO: should be moved to the config file
        cnn_output_size = d
        embedding_size = 300  # TODO: should be moved to the config file

        # instantiate sentence encoder 
        self.cnn = sent_encoder(embedding_dim=(embedding_size + 2 * pos_embed_output_size), num_filters=cnn_size,
                                ngram_filter_sizes=(2, 3, 4, 5),
                                conv_layer_activation=torch.nn.ReLU(), output_dim=cnn_output_size)

        # dropout after word embedding
        self.dropout = nn.Dropout(p=self.dropout_weight)

        #  given a sentence, returns its unnormalized attention weight
        self.attention_ff = nn.Sequential(
                nn.Linear(cnn_output_size, d),
                nn.ReLU(),
                nn.Linear(d, 1)
        )

        self.ff_before_alpha = nn.Sequential(
                nn.Linear(1, 50),
                nn.ReLU(),
                nn.Linear(50, 1),
        )
        # self.ff_before_alpha.unsqueeze(-1)
        ff_input_size = cnn_output_size
        if self.with_entity_embeddings:
            ff_input_size += embedding_size

        # output layer
        self.ff = nn.Sequential(
                nn.Linear(ff_input_size, d),
                nn.ReLU(),
                nn.Linear(d, self.num_classes)
        )

        self.loss = torch.nn.BCEWithLogitsLoss()  # sigmoid + binary cross entropy
        self.metrics = {}
        self.metrics['ap'] = MultilabelAveragePrecision()  # average precision = AUC
        self.metrics['bag_loss'] = Average()  # to display bag-level loss

        if self.sent_loss_weight > 0:
            self.metrics['sent_loss'] = Average()  # to display sentence-level loss

    # @overrides
    def forward(self,  # pylint: disable=arguments-differ
                mentions,
                positions1,
                positions2,
                is_direct_supervision_bag,
                sent_labels,  # sentence-level labels 
                labels
                ):

        # is all instances in this batch directly or distantly supervised
        is_direct_supervision_batch = bool(is_direct_supervision_bag['tokens'].shape[1] - 1)

        if is_direct_supervision_bag['tokens'].shape[1] != 1:
            direct_supervision_bags_count = sum(is_direct_supervision_bag['tokens'][:, -1] != 0).item()
            # is it a mix of both ? this affects a single batch because of the sorting_keys in the bucket iterator 
            if direct_supervision_bags_count != len(is_direct_supervision_bag['tokens'][:, -1] != 0):
                log.error("Mixed batch with %d supervised bags. Treated as dist. supervised", direct_supervision_bags_count)

        tokens = mentions['tokens']
        assert tokens.dim() == 3
        batch_size = tokens.size(0)
        padded_bag_size = tokens.size(1)
        padded_sent_size = tokens.size(2)
        mask = util.get_text_field_mask(mentions, num_wrapping_dims=1)

        # embed text
        t_embd = self.text_field_embedder.forward(mentions)

        # embed position information
        p1_embd = self.pos_embed.forward(positions1)
        p2_embd = self.pos_embed.forward(positions2)

        # concatinate position emebddings to the word embeddings
        # x.shape: batch_size x padded_bag_size x padded_sent_size x (text_embedding_size + 2 * position_embedding_size)
        x = torch.cat([t_embd, p1_embd, p2_embd], dim=3)

        if self.dropout_weight > 0:
            x = self.dropout(x)

        # merge the first two dimensions becase sentence encoder doesn't support the 4d input
        x = x.view(batch_size * padded_bag_size, padded_sent_size, -1) 
        mask = mask.view(batch_size * padded_bag_size, -1)

        # call sequence encoder
        x = self.cnn.forward(x, mask)  # (batch_size * padded_bag_size) x cnn_output_size

        # separate the first two dimensions back
        x = x.view(batch_size, padded_bag_size, -1)
        mask = mask.view(batch_size, padded_bag_size, -1)
       
        # compute unnormalized attention weights, one scaler per sentence
        alphas = self.attention_ff.forward(x)

        if self.sent_loss_weight > 0:
            # compute sentence-level loss on the directly supervised data (if any)
            sent_labels = sent_labels.unsqueeze(-1)
            # `sent_labels != 2`: directly supervised examples and distantly supervised negative examples
            sent_labels_mask = ((sent_labels != 2).long() * mask[:, :, [0]]).float()
            sent_labels_masked_pred = sent_labels_mask * torch.sigmoid(alphas)
            sent_labels_masked_goal = sent_labels_mask * sent_labels.float()
            sent_loss = torch.nn.functional.binary_cross_entropy(sent_labels_masked_pred, sent_labels_masked_goal)

        # apply a small FF to the attention weights
        alphas = self.ff_before_alpha.forward(alphas)

        # normalize attention weights based on the selected weighting function 
        if self.attention_weight_fn == 'uniform':
            alphas = mask[:, :, 0].float()
        elif self.attention_weight_fn == 'softmax':
            alphas = util.masked_softmax(alphas.squeeze(-1), mask[:, :, 0].float())
        elif self.attention_weight_fn == 'sigmoid':
            alphas = torch.sigmoid(alphas.squeeze(-1)) * mask[:, :, 0].float()
        elif self.attention_weight_fn == 'norm_sigmoid':  # equation 7 in https://arxiv.org/pdf/1805.02214.pdf
            alphas = torch.sigmoid(alphas.squeeze(-1)) * mask[:, :, 0].float()
            alphas = alphas / alphas.sum(dim=-1, keepdim=True)
        else:
            assert False

        # Input: 
        #   `x`: sentence encodings
        #   `alphas`: attention weights
        #   `attention_aggregation_fn`: aggregation function
        # Output: bag encoding
        if self.attention_aggregation_fn == 'max':
            x = alphas.unsqueeze(-1) * x  # weight sentences
            x = x.max(dim=1)[0]  # max pooling
        elif self.attention_aggregation_fn == 'avg':
            x = torch.bmm(alphas.unsqueeze(1), x).squeeze(1)  # average pooling
        else:
            assert False

        if self.with_entity_embeddings:
            # actual bag_size (not padded_bag_size) for each instance in the batch
            bag_size = mask[:, :, 0].sum(dim=1, keepdim=True).float()

            e1_mask = (positions1 == 0).long() * mask
            e1_embd = torch.matmul(e1_mask.unsqueeze(2).float(), t_embd)
            e1_embd_sent_sum = e1_embd.squeeze(dim=2).sum(dim=1)
            e1_embd_sent_avg = e1_embd_sent_sum / bag_size

            e2_mask = (positions2 == 0).long() * mask
            e2_embd = torch.matmul(e2_mask.unsqueeze(2).float(), t_embd)
            e2_embd_sent_sum = e2_embd.squeeze(dim=2).sum(dim=1)
            e2_embd_sent_avg = e2_embd_sent_sum / bag_size

            e1_e2_mult = e1_embd_sent_avg * e2_embd_sent_avg
            x = torch.cat([x, e1_e2_mult], dim=1)

        logits = self.ff.forward(x)  # batch_size x self.num_classes
        output_dict = {'logits': logits}  # sigmoid is applied in the loss function and the metric class, not here

        if labels is not None:  # Training and evaluation
            w = self.sent_loss_weight / (self.sent_loss_weight + 1)
            one_minus_w = 1 - w  # weight of the bag-level loss

            if is_direct_supervision_batch and self.sent_loss_weight > 0:
                one_minus_w = 0

            loss = self.loss(logits, labels.squeeze(-1).type_as(logits)) * self.num_classes  # scale the loss to be more readable
            loss *= one_minus_w
            self.metrics['bag_loss'](loss.item())
            self.metrics['ap'](logits, labels.squeeze(-1))

            if self.sent_loss_weight > 0:
                sent_loss *= w
                self.metrics['sent_loss'](sent_loss.item())
                loss += sent_loss
            output_dict['loss'] = loss
        return output_dict

    # @overrides # Edit: dict
    def decode(self, output_dict:Any)->Any:
        prob_thr = 0.6  # to ignore predicted labels with low prob. 
        probs = torch.sigmoid(output_dict['logits'])
        output_dict['labels'] = []
        for row in probs.cpu().data.numpy():
            labels = []
            for i, p in enumerate(row):
                if p > prob_thr:  # ignore predictions with low prob.
                    labels.append((self.vocab.get_token_from_index(i, namespace="labels"), float(p)))
                    # output_dict[self.vocab.get_token_from_index(i, namespace="labels")] = torch.Tensor([float(p)])
            output_dict['labels'].append(labels)
        del output_dict['loss']
        return output_dict

    # @overrides
    def get_metrics(self, reset = False):
        return {metric_name: metric.get_metric(reset) for metric_name, metric in self.metrics.items()}

logger = logging.getLogger(__name__)  # pylint: disable=invalid-name
class MultilabelAveragePrecision(Metric):
    """
    Average precision for multiclass multilabel classification. Average precision
    approximately equals area under the precision-recall curve.
    - Average precision: scikit-learn.org/stable/modules/generated/sklearn.metrics.average_precision_score.html
    - Precision/recall: this is multilabel metric, so all labels are considered predictions (with their
        corresponding confidences) not just the one with the highest confidence.

    Two modes of calculating AP are implemented,
        - a fast but less accurate implementation that bins threshold. Supports the frequent use of get_metrics
        - a more accurate implemenatition when get_metrics(reset=True)
    The fast one tends to underestimate AP.
    AP - Fast_AP < 10/number_of_bins
    """
    recall_thr:float
    sigmoid:nn.Sigmoid
    predictions:np.ndarray
    gold_labels:np.ndarray
    bins:int
    bin_size:float
    correct_counts:np.ndarray
    total_counts:np.ndarray
    def __init__(self, bins=1000, recall_thr = 0.40):
        """Args:
            bins: number of threshold bins for the fast computation of AP
            recall_thr: compute AP (or AUC) for recall values [0:recall_thr]
        """
        self.recall_thr = recall_thr

        self.sigmoid = nn.Sigmoid()

        # stores data for the accurate calculation of AP
        self.predictions = np.array([])
        self.gold_labels = np.array([])

        # stored data for the fast calculation of AP
        self.bins = bins
        self.bin_size = 1.0/self.bins
        self.correct_counts = np.array([0] * self.bins)
        self.total_counts = np.array([0] * self.bins)

    def __call__(self,
                 predictions,
                 gold_labels):
        predictions = self.sigmoid.forward(predictions)  # sigmoid to make sure all values are [0:1]

        # Get the data from the Variables to avoid GPU memory leak
        # predictions, gold_labels = self.unwrap_to_tensors(predictions, gold_labels)

        # Sanity check
        if gold_labels.shape != predictions.shape:
            raise ConfigurationError("gold_labels must have the same shape of predictions. "
                                     "Found shapes {} and {}".format(gold_labels.shape, predictions.shape))

        pred = predictions.numpy().ravel()
        gold = gold_labels.numpy().ravel()

        # udpate data of accurate computation of AP
        self.predictions = np.append(self.predictions, pred)
        self.gold_labels = np.append(self.gold_labels, gold)

        # update data of fast computation of AP
        idx = (self.bins - 1) - np.minimum((pred/self.bin_size).astype(int), self.bins - 1)

        gold_uniq_idx, gold_idx_count = np.unique(idx[np.nonzero(gold)], return_counts=True)
        self.correct_counts[gold_uniq_idx] = np.add(self.correct_counts[gold_uniq_idx], gold_idx_count)

        uniq_idx, idx_count = np.unique(idx, return_counts=True)
        self.total_counts[uniq_idx] = np.add(self.total_counts[uniq_idx], idx_count)

    def _thresholded_average_precision_score(self, precision, recall):
        if len(precision) == 0:
            return 0, -1
        index = np.argmin(abs(recall - self.recall_thr))
        filtered_precision = precision[:index + 1]
        filtered_recall = recall[:index + 1]
        ap = np.sum(np.diff(np.insert(filtered_recall, 0, 0)) * filtered_precision)
        return ap, index  # index of the value with recall = self.recall_thr (useful for logging)


    def get_metric(self, reset = False):
        """
        Returns average precision.

        If reset=False, returns the fast AP.
        If reset=True, returns accurate AP, logs difference ebtween accurate and fast AP and
                       logs a list of points on the precision-recall curve.

        """
        correct_cumsum = np.cumsum(self.correct_counts)
        precision = correct_cumsum  / np.cumsum(self.total_counts)
        recall = correct_cumsum  / correct_cumsum[-1]
        isfinite = np.isfinite(precision)
        precision = precision[isfinite]
        recall = recall[isfinite]
        ap, index = self._thresholded_average_precision_score(precision, recall)  # fast AP because of binned values
        if reset:
            fast_ap = ap
            precision, recall, thresholds = precision_recall_curve(self.gold_labels, self.predictions)

            # _thresholded_average_precision_score assumes precision is descending and recall is ascending
            precision = precision[::-1]
            recall = recall[::-1]
            thresholds = thresholds[::-1]
            ap, index = self._thresholded_average_precision_score(precision, recall)  # accurate AP because of using all values
            logger.info("Fast AP: %0.4f -- Accurate AP: %0.4f", fast_ap, ap)
            if index >= len(thresholds):
                logger.info("Index = %d but len(thresholds) = %d. Change index to point to the end of the list.",
                            index, len(thresholds))
                index = len(thresholds) - 1
            logger.info("at index %d/%d (top %%%0.4f) -- threshold: %0.4f",
                        index, len(self.gold_labels), 100.0 * index / len(self.gold_labels), thresholds[index])

            # only keep the top predictions then reverse again for printing (to draw the AUC curve)
            precision = precision[:index + 1][::-1]
            recall = recall[:index + 1][::-1]
            thresholds = thresholds[:index + 1][::-1]

            next_step = thresholds[0]
            step_size = 0.005
            max_skip = int(len(thresholds) / 500)
            skipped = 0
            logger.info("Precision-Recall curve ... ")
            logger.info("precision, recall, threshold")
            for p, r, t in [x for x in zip(precision, recall, thresholds)]:
                if t < next_step and skipped < max_skip:
                    skipped += 1
                    continue
                skipped = 0
                next_step += step_size
                # logger.info("%0.4f, %0.4f, %0.4f", p, r, t)
            self.reset()
        return ap

    def reset(self):
        self.predictions = np.array([])
        self.gold_labels = np.array([])

        self.correct_counts = np.array([0] * self.bins)
        self.total_counts = np.array([0] * self.bins)

# @DatasetReader.register("relation_instances")


    
class RelationExtractionPredictor(Predictor):
    """"Predictor wrapper for the RelationExtractionPredictor"""
    _dataset_reader: RelationInstancesReader
    def _json_to_instance(self, json_dict):
        e1 = json_dict['e1']
        e2 = json_dict['e2']
        mentions = json_dict['mentions']

        instance = self._dataset_reader.text_to_instance(
                e1=e1, e2=e2, rels=[], mentions=mentions, is_predict=True, supervision_type=False)
        if not instance:
            log.error('parsing instance failed: %s', mentions)
            instance = self._dataset_reader.text_to_instance(
                    e1="e1", e2="e2", rels=[],
                    mentions=["Some relation between <e1>entity 1</e1> and <e2>entity 2</e2>"],
                    is_predict=True, supervision_type=False)
        return instance, {}


